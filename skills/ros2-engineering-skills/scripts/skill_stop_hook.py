#!/usr/bin/env python3
"""Skills 2.0 Stop Hook — Post-execution validation for ros2-engineering-skills.

This hook runs when the skill execution stops. It validates that any generated
ROS 2 artifacts (packages, launch files, QoS configurations) conform to the
skill's engineering principles.

Exit codes:
    0 — All checks passed
    1 — Validation issues found (reported to stdout as JSON)
"""

import json
import os
import sys
import ast


def find_generated_launch_files(workspace):
    """Find all .launch.py files in the workspace."""
    launch_files = []
    for root, _dirs, files in os.walk(workspace):
        # Skip hidden dirs, build, install, log
        if any(part.startswith('.') or part in ('build', 'install', 'log')
               for part in root.split(os.sep)):
            continue
        for f in files:
            if f.endswith('.launch.py'):
                launch_files.append(os.path.join(root, f))
    return launch_files


def validate_launch_file_syntax(filepath):
    """Check that a launch file is valid Python and has generate_launch_description."""
    issues = []
    try:
        with open(filepath, 'r') as fh:
            source = fh.read()
        tree = ast.parse(source, filename=filepath)
        func_names = [
            node.name for node in ast.walk(tree)
            if isinstance(node, ast.FunctionDef)
        ]
        if 'generate_launch_description' not in func_names:
            issues.append({
                'file': filepath,
                'severity': 'error',
                'message': 'Missing generate_launch_description function',
            })
    except SyntaxError as e:
        issues.append({
            'file': filepath,
            'severity': 'error',
            'message': f'Syntax error: {e}',
        })
    except OSError:
        pass  # File may have been removed during session
    return issues


def validate_package_xml(filepath):
    """Check that a package.xml uses format 3 and has required elements."""
    issues = []
    try:
        import xml.etree.ElementTree as ET
        tree = ET.parse(filepath)
        root = tree.getroot()
        fmt = root.attrib.get('format', '')
        if fmt != '3':
            issues.append({
                'file': filepath,
                'severity': 'warning',
                'message': f'package.xml uses format {fmt}, recommend format 3',
            })
        if root.find('name') is None:
            issues.append({
                'file': filepath,
                'severity': 'error',
                'message': 'package.xml missing <name> element',
            })
        if root.find('license') is None:
            issues.append({
                'file': filepath,
                'severity': 'warning',
                'message': 'package.xml missing <license> element',
            })
    except Exception as e:
        issues.append({
            'file': filepath,
            'severity': 'error',
            'message': f'Failed to parse package.xml: {e}',
        })
    return issues


def find_package_xmls(workspace):
    """Find all package.xml files in the workspace."""
    results = []
    for root, _dirs, files in os.walk(workspace):
        if any(part.startswith('.') or part in ('build', 'install', 'log')
               for part in root.split(os.sep)):
            continue
        for f in files:
            if f == 'package.xml':
                results.append(os.path.join(root, f))
    return results


def main():
    workspace = os.environ.get('SKILL_WORKSPACE', os.getcwd())
    all_issues = []

    # Validate launch files
    for lf in find_generated_launch_files(workspace):
        all_issues.extend(validate_launch_file_syntax(lf))

    # Validate package.xml files
    for px in find_package_xmls(workspace):
        all_issues.extend(validate_package_xml(px))

    result = {
        'hook': 'ros2-engineering-skills:stop',
        'version': '1.0.0',
        'issues_count': len(all_issues),
        'issues': all_issues,
        'status': 'fail' if any(
            i['severity'] == 'error' for i in all_issues
        ) else 'pass',
    }

    print(json.dumps(result, indent=2))
    sys.exit(1 if result['status'] == 'fail' else 0)


if __name__ == '__main__':
    main()
