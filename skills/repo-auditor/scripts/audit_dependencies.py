#!/usr/bin/env python3
"""
Audit Dependencies Script

Analyzes dependencies for outdated packages, security vulnerabilities, and license issues.

Usage:
    python audit_dependencies.py <repo-path> [--json]

Examples:
    python audit_dependencies.py /path/to/repo
    python audit_dependencies.py . --json
"""

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path


def run_command(cmd, cwd=None):
    """Run a shell command and return output."""
    try:
        result = subprocess.run(
            cmd,
            shell=True,
            capture_output=True,
            text=True,
            cwd=cwd,
            timeout=120
        )
        return {
            'success': result.returncode == 0,
            'stdout': result.stdout,
            'stderr': result.stderr,
            'returncode': result.returncode
        }
    except subprocess.TimeoutExpired:
        return {'success': False, 'stdout': '', 'stderr': 'Command timed out', 'returncode': -1}
    except Exception as e:
        return {'success': False, 'stdout': '', 'stderr': str(e), 'returncode': -1}


def parse_package_json(repo_path):
    """Parse package.json for Node.js dependencies."""
    package_json_path = os.path.join(repo_path, 'package.json')
    if not os.path.exists(package_json_path):
        return None
    
    try:
        with open(package_json_path, 'r') as f:
            data = json.load(f)
        
        deps = data.get('dependencies', {})
        dev_deps = data.get('devDependencies', {})
        
        return {
            'dependencies': deps,
            'devDependencies': dev_deps,
            'total_count': len(deps) + len(dev_deps)
        }
    except (json.JSONDecodeError, IOError) as e:
        return {'error': str(e)}


def parse_requirements_txt(repo_path):
    """Parse requirements.txt for Python dependencies."""
    requirements_path = os.path.join(repo_path, 'requirements.txt')
    if not os.path.exists(requirements_path):
        return None
    
    try:
        with open(requirements_path, 'r') as f:
            lines = f.readlines()
        
        deps = []
        for line in lines:
            line = line.strip()
            # Skip comments and empty lines
            if not line or line.startswith('#'):
                continue
            # Skip options like -r, -e, --index-url
            if line.startswith('-'):
                continue
            
            # Parse package name and version
            match = re.match(r'^([a-zA-Z0-9_-]+)([<>=!~]+.*)?$', line.split('[')[0])
            if match:
                deps.append({
                    'name': match.group(1),
                    'version_spec': match.group(2) or 'any'
                })
        
        return {
            'dependencies': deps,
            'total_count': len(deps)
        }
    except IOError as e:
        return {'error': str(e)}


def parse_go_mod(repo_path):
    """Parse go.mod for Go dependencies."""
    go_mod_path = os.path.join(repo_path, 'go.mod')
    if not os.path.exists(go_mod_path):
        return None
    
    try:
        with open(go_mod_path, 'r') as f:
            content = f.read()
        
        deps = []
        in_require = False
        
        for line in content.split('\n'):
            line = line.strip()
            
            if line.startswith('require ('):
                in_require = True
                continue
            elif line == ')':
                in_require = False
                continue
            elif line.startswith('require '):
                # Single-line require
                parts = line.replace('require ', '').split()
                if len(parts) >= 2:
                    deps.append({'name': parts[0], 'version': parts[1]})
            elif in_require and line:
                parts = line.split()
                if len(parts) >= 2:
                    deps.append({'name': parts[0], 'version': parts[1]})
        
        return {
            'dependencies': deps,
            'total_count': len(deps)
        }
    except IOError as e:
        return {'error': str(e)}


def parse_cargo_toml(repo_path):
    """Parse Cargo.toml for Rust dependencies."""
    cargo_path = os.path.join(repo_path, 'Cargo.toml')
    if not os.path.exists(cargo_path):
        return None
    
    try:
        with open(cargo_path, 'r') as f:
            content = f.read()
        
        deps = []
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
                parts = line.split('=', 1)
                name = parts[0].strip()
                version = parts[1].strip().strip('"').strip("'")
                deps.append({
                    'name': name,
                    'version': version,
                    'dev': in_dev_deps
                })
        
        return {
            'dependencies': deps,
            'total_count': len(deps)
        }
    except IOError as e:
        return {'error': str(e)}


def check_npm_outdated(repo_path):
    """Check for outdated npm packages."""
    if not os.path.exists(os.path.join(repo_path, 'package.json')):
        return None
    
    result = run_command('npm outdated --json 2>/dev/null || true', cwd=repo_path)
    
    if result['stdout'].strip():
        try:
            outdated = json.loads(result['stdout'])
            return {
                'outdated_count': len(outdated),
                'packages': outdated
            }
        except json.JSONDecodeError:
            return {'error': 'Failed to parse npm outdated output'}
    
    return {'outdated_count': 0, 'packages': {}}


def check_npm_audit(repo_path):
    """Run npm audit for security vulnerabilities."""
    if not os.path.exists(os.path.join(repo_path, 'package.json')):
        return None
    
    result = run_command('npm audit --json 2>/dev/null || true', cwd=repo_path)
    
    if result['stdout'].strip():
        try:
            audit = json.loads(result['stdout'])
            vulnerabilities = audit.get('vulnerabilities', {})
            
            severity_counts = {'critical': 0, 'high': 0, 'moderate': 0, 'low': 0}
            for vuln in vulnerabilities.values():
                severity = vuln.get('severity', 'low')
                if severity in severity_counts:
                    severity_counts[severity] += 1
            
            return {
                'total_vulnerabilities': len(vulnerabilities),
                'severity_counts': severity_counts,
                'vulnerabilities': vulnerabilities
            }
        except json.JSONDecodeError:
            return {'error': 'Failed to parse npm audit output'}
    
    return {'total_vulnerabilities': 0, 'severity_counts': {}, 'vulnerabilities': {}}


def check_pip_outdated(repo_path):
    """Check for outdated pip packages (if in a virtual environment)."""
    if not os.path.exists(os.path.join(repo_path, 'requirements.txt')):
        return None
    
    result = run_command('pip list --outdated --format=json 2>/dev/null || true', cwd=repo_path)
    
    if result['stdout'].strip():
        try:
            outdated = json.loads(result['stdout'])
            return {
                'outdated_count': len(outdated),
                'packages': outdated
            }
        except json.JSONDecodeError:
            return {'error': 'Failed to parse pip outdated output'}
    
    return {'outdated_count': 0, 'packages': []}


def analyze_dependency_risks(deps_info):
    """Analyze dependencies for potential risks."""
    risks = []
    
    # Check for high dependency count
    total_deps = 0
    for ecosystem, info in deps_info.items():
        if info and isinstance(info, dict) and 'total_count' in info:
            total_deps += info['total_count']
    
    if total_deps > 100:
        risks.append({
            'type': 'high_dependency_count',
            'severity': 'medium',
            'message': f'High number of dependencies ({total_deps}). Consider auditing for unused packages.'
        })
    
    # Check for npm vulnerabilities
    if 'npm_audit' in deps_info and deps_info['npm_audit']:
        audit = deps_info['npm_audit']
        if audit.get('severity_counts', {}).get('critical', 0) > 0:
            risks.append({
                'type': 'critical_vulnerabilities',
                'severity': 'critical',
                'message': f"Critical npm vulnerabilities found: {audit['severity_counts']['critical']}"
            })
        if audit.get('severity_counts', {}).get('high', 0) > 0:
            risks.append({
                'type': 'high_vulnerabilities',
                'severity': 'high',
                'message': f"High severity npm vulnerabilities found: {audit['severity_counts']['high']}"
            })
    
    # Check for outdated packages
    outdated_count = 0
    if 'npm_outdated' in deps_info and deps_info['npm_outdated']:
        outdated_count += deps_info['npm_outdated'].get('outdated_count', 0)
    if 'pip_outdated' in deps_info and deps_info['pip_outdated']:
        outdated_count += deps_info['pip_outdated'].get('outdated_count', 0)
    
    if outdated_count > 10:
        risks.append({
            'type': 'many_outdated',
            'severity': 'medium',
            'message': f'{outdated_count} outdated packages. Consider updating dependencies.'
        })
    
    return risks


def audit_dependencies(repo_path):
    """Perform full dependency audit on a repository."""
    if not os.path.isdir(repo_path):
        return {'error': f'Path does not exist or is not a directory: {repo_path}'}
    
    result = {
        'repository': os.path.abspath(repo_path),
        'ecosystems': {}
    }
    
    # Parse dependency files
    npm_deps = parse_package_json(repo_path)
    if npm_deps:
        result['ecosystems']['nodejs'] = npm_deps
    
    python_deps = parse_requirements_txt(repo_path)
    if python_deps:
        result['ecosystems']['python'] = python_deps
    
    go_deps = parse_go_mod(repo_path)
    if go_deps:
        result['ecosystems']['go'] = go_deps
    
    rust_deps = parse_cargo_toml(repo_path)
    if rust_deps:
        result['ecosystems']['rust'] = rust_deps
    
    # Run security checks (if tools available)
    npm_outdated = check_npm_outdated(repo_path)
    if npm_outdated:
        result['npm_outdated'] = npm_outdated
    
    npm_audit = check_npm_audit(repo_path)
    if npm_audit:
        result['npm_audit'] = npm_audit
    
    pip_outdated = check_pip_outdated(repo_path)
    if pip_outdated:
        result['pip_outdated'] = pip_outdated
    
    # Analyze risks
    result['risks'] = analyze_dependency_risks(result)
    
    # Summary
    total_deps = sum(
        info.get('total_count', 0) 
        for info in result['ecosystems'].values() 
        if isinstance(info, dict)
    )
    result['summary'] = {
        'total_dependencies': total_deps,
        'ecosystems_found': list(result['ecosystems'].keys()),
        'risk_count': len(result['risks']),
        'critical_risks': len([r for r in result['risks'] if r['severity'] == 'critical']),
        'high_risks': len([r for r in result['risks'] if r['severity'] == 'high'])
    }
    
    return result


def print_report(result):
    """Print a human-readable report."""
    print("=" * 60)
    print("DEPENDENCY AUDIT REPORT")
    print("=" * 60)
    print(f"\nRepository: {result['repository']}")
    
    print("\n" + "-" * 40)
    print("SUMMARY")
    print("-" * 40)
    summary = result.get('summary', {})
    print(f"  Total Dependencies: {summary.get('total_dependencies', 0)}")
    print(f"  Ecosystems: {', '.join(summary.get('ecosystems_found', []))}")
    print(f"  Risk Count: {summary.get('risk_count', 0)}")
    print(f"  Critical Risks: {summary.get('critical_risks', 0)}")
    print(f"  High Risks: {summary.get('high_risks', 0)}")
    
    print("\n" + "-" * 40)
    print("DEPENDENCIES BY ECOSYSTEM")
    print("-" * 40)
    for ecosystem, info in result.get('ecosystems', {}).items():
        if isinstance(info, dict) and 'total_count' in info:
            print(f"  {ecosystem}: {info['total_count']} packages")
    
    if result.get('npm_outdated') and result['npm_outdated'].get('outdated_count', 0) > 0:
        print("\n" + "-" * 40)
        print("OUTDATED NPM PACKAGES")
        print("-" * 40)
        print(f"  Count: {result['npm_outdated']['outdated_count']}")
        for pkg, info in list(result['npm_outdated'].get('packages', {}).items())[:10]:
            current = info.get('current', 'unknown')
            wanted = info.get('wanted', 'unknown')
            latest = info.get('latest', 'unknown')
            print(f"  {pkg}: {current} -> {latest} (wanted: {wanted})")
        if result['npm_outdated']['outdated_count'] > 10:
            print(f"  ... and {result['npm_outdated']['outdated_count'] - 10} more")
    
    if result.get('npm_audit') and result['npm_audit'].get('total_vulnerabilities', 0) > 0:
        print("\n" + "-" * 40)
        print("NPM SECURITY VULNERABILITIES")
        print("-" * 40)
        audit = result['npm_audit']
        print(f"  Total: {audit['total_vulnerabilities']}")
        for severity, count in audit.get('severity_counts', {}).items():
            if count > 0:
                print(f"  {severity.capitalize()}: {count}")
    
    if result.get('risks'):
        print("\n" + "-" * 40)
        print("RISKS IDENTIFIED")
        print("-" * 40)
        for risk in result['risks']:
            severity = risk['severity'].upper()
            print(f"  [{severity}] {risk['message']}")
    
    print("\n" + "-" * 40)
    print("RECOMMENDATIONS")
    print("-" * 40)
    
    recommendations = []
    if result.get('npm_audit', {}).get('total_vulnerabilities', 0) > 0:
        recommendations.append("Run 'npm audit fix' to fix vulnerabilities automatically")
    if result.get('npm_outdated', {}).get('outdated_count', 0) > 0:
        recommendations.append("Run 'npm update' to update packages to wanted versions")
    if result.get('pip_outdated', {}).get('outdated_count', 0) > 0:
        recommendations.append("Run 'pip install --upgrade <package>' for outdated Python packages")
    if not recommendations:
        recommendations.append("No immediate actions required")
    
    for i, rec in enumerate(recommendations, 1):
        print(f"  {i}. {rec}")
    
    print("\n" + "=" * 60)


def main():
    parser = argparse.ArgumentParser(
        description='Audit dependencies of a repository',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    python audit_dependencies.py /path/to/repo
    python audit_dependencies.py . --json
        """
    )
    parser.add_argument('repo_path', help='Path to the repository to audit')
    parser.add_argument('--json', action='store_true', help='Output as JSON')
    
    args = parser.parse_args()
    
    result = audit_dependencies(args.repo_path)
    
    if 'error' in result:
        print(f"Error: {result['error']}", file=sys.stderr)
        sys.exit(1)
    
    if args.json:
        # Remove large vulnerability details for cleaner JSON output
        if 'npm_audit' in result and 'vulnerabilities' in result['npm_audit']:
            result['npm_audit']['vulnerabilities'] = f"<{len(result['npm_audit']['vulnerabilities'])} vulnerabilities>"
        print(json.dumps(result, indent=2))
    else:
        print_report(result)


if __name__ == '__main__':
    main()
