#!/usr/bin/env python3
"""
Find Dead Code Script

Identifies unused functions, classes, imports, and variables in a repository.

Usage:
    python find_dead_code.py <repo-path> [--language <lang>] [--json]

Examples:
    python find_dead_code.py /path/to/repo
    python find_dead_code.py . --language python
    python find_dead_code.py . --json
"""

import argparse
import json
import os
import re
import subprocess
import sys
from collections import defaultdict
from pathlib import Path


# Directories to skip
SKIP_DIRS = {
    'node_modules', 'venv', '.venv', 'env', '.env', '__pycache__',
    '.git', '.svn', 'vendor', 'target', 'build', 'dist', 'out',
    '.next', '.nuxt', 'coverage', '.pytest_cache', '.mypy_cache',
    'site-packages', 'eggs', '.eggs', '.tox'
}


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


def find_python_files(repo_path):
    """Find all Python files in the repository."""
    python_files = []
    for root, dirs, files in os.walk(repo_path):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for file in files:
            if file.endswith('.py'):
                python_files.append(os.path.join(root, file))
    return python_files


def find_js_ts_files(repo_path):
    """Find all JavaScript/TypeScript files in the repository."""
    js_files = []
    extensions = ('.js', '.jsx', '.ts', '.tsx', '.mjs', '.cjs')
    for root, dirs, files in os.walk(repo_path):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for file in files:
            if file.endswith(extensions):
                js_files.append(os.path.join(root, file))
    return js_files


def extract_python_definitions(file_path):
    """Extract function and class definitions from a Python file."""
    definitions = {
        'functions': [],
        'classes': [],
        'imports': []
    }
    
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
            lines = content.split('\n')
        
        for i, line in enumerate(lines, 1):
            # Find function definitions
            func_match = re.match(r'^(?:async\s+)?def\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*\(', line)
            if func_match:
                func_name = func_match.group(1)
                # Skip private/magic methods for now
                if not func_name.startswith('__'):
                    definitions['functions'].append({
                        'name': func_name,
                        'line': i,
                        'file': file_path
                    })
            
            # Find class definitions
            class_match = re.match(r'^class\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*[:\(]', line)
            if class_match:
                definitions['classes'].append({
                    'name': class_match.group(1),
                    'line': i,
                    'file': file_path
                })
            
            # Find imports
            import_match = re.match(r'^(?:from\s+[\w.]+\s+)?import\s+(.+)$', line)
            if import_match:
                imports_str = import_match.group(1)
                # Handle "import x, y, z" and "from x import a, b, c"
                for imp in imports_str.split(','):
                    imp = imp.strip()
                    # Handle "import x as y"
                    if ' as ' in imp:
                        imp = imp.split(' as ')[1].strip()
                    # Handle "from x import (a, b)"
                    imp = imp.strip('()')
                    if imp and not imp.startswith('*'):
                        definitions['imports'].append({
                            'name': imp,
                            'line': i,
                            'file': file_path
                        })
    except Exception as e:
        pass
    
    return definitions


def extract_js_definitions(file_path):
    """Extract function and class definitions from a JavaScript/TypeScript file."""
    definitions = {
        'functions': [],
        'classes': [],
        'exports': []
    }
    
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
            lines = content.split('\n')
        
        for i, line in enumerate(lines, 1):
            # Find function definitions
            func_patterns = [
                r'(?:export\s+)?(?:async\s+)?function\s+([a-zA-Z_$][a-zA-Z0-9_$]*)\s*\(',
                r'(?:const|let|var)\s+([a-zA-Z_$][a-zA-Z0-9_$]*)\s*=\s*(?:async\s+)?\(',
                r'(?:const|let|var)\s+([a-zA-Z_$][a-zA-Z0-9_$]*)\s*=\s*(?:async\s+)?function',
            ]
            
            for pattern in func_patterns:
                func_match = re.search(pattern, line)
                if func_match:
                    definitions['functions'].append({
                        'name': func_match.group(1),
                        'line': i,
                        'file': file_path
                    })
                    break
            
            # Find class definitions
            class_match = re.search(r'(?:export\s+)?class\s+([a-zA-Z_$][a-zA-Z0-9_$]*)', line)
            if class_match:
                definitions['classes'].append({
                    'name': class_match.group(1),
                    'line': i,
                    'file': file_path
                })
            
            # Find exports
            export_match = re.search(r'export\s+(?:default\s+)?(?:const|let|var|function|class)?\s*([a-zA-Z_$][a-zA-Z0-9_$]*)', line)
            if export_match:
                definitions['exports'].append({
                    'name': export_match.group(1),
                    'line': i,
                    'file': file_path
                })
    except Exception as e:
        pass
    
    return definitions


def find_usages(repo_path, name, file_extensions):
    """Find usages of a name in the repository."""
    usages = []
    
    for root, dirs, files in os.walk(repo_path):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for file in files:
            if any(file.endswith(ext) for ext in file_extensions):
                file_path = os.path.join(root, file)
                try:
                    with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                        content = f.read()
                    
                    # Use word boundary matching
                    pattern = r'\b' + re.escape(name) + r'\b'
                    matches = list(re.finditer(pattern, content))
                    
                    if matches:
                        usages.append({
                            'file': file_path,
                            'count': len(matches)
                        })
                except Exception:
                    pass
    
    return usages


def analyze_python_dead_code(repo_path):
    """Analyze Python code for potentially dead code."""
    results = {
        'potentially_unused_functions': [],
        'potentially_unused_classes': [],
        'unused_imports': [],
        'commented_code_blocks': []
    }
    
    python_files = find_python_files(repo_path)
    
    if not python_files:
        return results
    
    # Collect all definitions
    all_functions = []
    all_classes = []
    all_imports = []
    
    for file_path in python_files:
        defs = extract_python_definitions(file_path)
        all_functions.extend(defs['functions'])
        all_classes.extend(defs['classes'])
        all_imports.extend(defs['imports'])
    
    # Check for unused functions (defined but only referenced once - at definition)
    for func in all_functions:
        usages = find_usages(repo_path, func['name'], ['.py'])
        total_usage_count = sum(u['count'] for u in usages)
        
        # If only used once (the definition itself), it might be unused
        if total_usage_count <= 1:
            results['potentially_unused_functions'].append({
                'name': func['name'],
                'file': os.path.relpath(func['file'], repo_path),
                'line': func['line'],
                'usage_count': total_usage_count
            })
    
    # Check for unused classes
    for cls in all_classes:
        usages = find_usages(repo_path, cls['name'], ['.py'])
        total_usage_count = sum(u['count'] for u in usages)
        
        if total_usage_count <= 1:
            results['potentially_unused_classes'].append({
                'name': cls['name'],
                'file': os.path.relpath(cls['file'], repo_path),
                'line': cls['line'],
                'usage_count': total_usage_count
            })
    
    # Find commented-out code blocks
    for file_path in python_files:
        try:
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                lines = f.readlines()
            
            consecutive_comments = 0
            comment_start = 0
            
            for i, line in enumerate(lines, 1):
                stripped = line.strip()
                if stripped.startswith('#') and len(stripped) > 1:
                    # Check if it looks like code
                    comment_content = stripped[1:].strip()
                    if re.match(r'^(def |class |import |from |if |for |while |return |print\()', comment_content):
                        if consecutive_comments == 0:
                            comment_start = i
                        consecutive_comments += 1
                else:
                    if consecutive_comments >= 3:
                        results['commented_code_blocks'].append({
                            'file': os.path.relpath(file_path, repo_path),
                            'start_line': comment_start,
                            'lines': consecutive_comments
                        })
                    consecutive_comments = 0
        except Exception:
            pass
    
    return results


def analyze_js_dead_code(repo_path):
    """Analyze JavaScript/TypeScript code for potentially dead code."""
    results = {
        'potentially_unused_functions': [],
        'potentially_unused_classes': [],
        'potentially_unused_exports': []
    }
    
    js_files = find_js_ts_files(repo_path)
    
    if not js_files:
        return results
    
    # Collect all definitions
    all_functions = []
    all_classes = []
    all_exports = []
    
    for file_path in js_files:
        defs = extract_js_definitions(file_path)
        all_functions.extend(defs['functions'])
        all_classes.extend(defs['classes'])
        all_exports.extend(defs['exports'])
    
    extensions = ['.js', '.jsx', '.ts', '.tsx', '.mjs', '.cjs']
    
    # Check for unused functions
    for func in all_functions:
        usages = find_usages(repo_path, func['name'], extensions)
        total_usage_count = sum(u['count'] for u in usages)
        
        if total_usage_count <= 1:
            results['potentially_unused_functions'].append({
                'name': func['name'],
                'file': os.path.relpath(func['file'], repo_path),
                'line': func['line'],
                'usage_count': total_usage_count
            })
    
    # Check for unused classes
    for cls in all_classes:
        usages = find_usages(repo_path, cls['name'], extensions)
        total_usage_count = sum(u['count'] for u in usages)
        
        if total_usage_count <= 1:
            results['potentially_unused_classes'].append({
                'name': cls['name'],
                'file': os.path.relpath(cls['file'], repo_path),
                'line': cls['line'],
                'usage_count': total_usage_count
            })
    
    return results


def run_external_tools(repo_path):
    """Run external dead code detection tools if available."""
    tool_results = {}
    
    # Try vulture for Python
    if find_python_files(repo_path):
        result = run_command('vulture . --min-confidence 80 2>/dev/null', cwd=repo_path)
        if result['success'] or result['stdout']:
            tool_results['vulture'] = {
                'available': True,
                'output': result['stdout'][:2000] if result['stdout'] else 'No issues found'
            }
        else:
            tool_results['vulture'] = {
                'available': False,
                'message': 'vulture not installed. Install with: pip install vulture'
            }
    
    # Try eslint for JavaScript
    if find_js_ts_files(repo_path):
        result = run_command('npx eslint . --rule "no-unused-vars: error" --format json 2>/dev/null | head -100', cwd=repo_path)
        if result['success']:
            tool_results['eslint'] = {
                'available': True,
                'output': 'ESLint check completed'
            }
        else:
            tool_results['eslint'] = {
                'available': False,
                'message': 'ESLint not available or not configured'
            }
    
    return tool_results


def find_dead_code(repo_path, language=None):
    """Perform dead code analysis on a repository."""
    if not os.path.isdir(repo_path):
        return {'error': f'Path does not exist or is not a directory: {repo_path}'}
    
    result = {
        'repository': os.path.abspath(repo_path),
        'analysis': {}
    }
    
    # Analyze Python if requested or if Python files exist
    if language in (None, 'python'):
        python_results = analyze_python_dead_code(repo_path)
        if any(python_results.values()):
            result['analysis']['python'] = python_results
    
    # Analyze JavaScript/TypeScript if requested or if JS files exist
    if language in (None, 'javascript', 'typescript', 'js', 'ts'):
        js_results = analyze_js_dead_code(repo_path)
        if any(js_results.values()):
            result['analysis']['javascript'] = js_results
    
    # Try external tools
    result['external_tools'] = run_external_tools(repo_path)
    
    # Summary
    total_unused_functions = 0
    total_unused_classes = 0
    total_commented_blocks = 0
    
    for lang, analysis in result['analysis'].items():
        total_unused_functions += len(analysis.get('potentially_unused_functions', []))
        total_unused_classes += len(analysis.get('potentially_unused_classes', []))
        total_commented_blocks += len(analysis.get('commented_code_blocks', []))
    
    result['summary'] = {
        'potentially_unused_functions': total_unused_functions,
        'potentially_unused_classes': total_unused_classes,
        'commented_code_blocks': total_commented_blocks,
        'languages_analyzed': list(result['analysis'].keys())
    }
    
    return result


def print_report(result):
    """Print a human-readable report."""
    print("=" * 60)
    print("DEAD CODE ANALYSIS REPORT")
    print("=" * 60)
    print(f"\nRepository: {result['repository']}")
    
    print("\n" + "-" * 40)
    print("SUMMARY")
    print("-" * 40)
    summary = result.get('summary', {})
    print(f"  Potentially Unused Functions: {summary.get('potentially_unused_functions', 0)}")
    print(f"  Potentially Unused Classes: {summary.get('potentially_unused_classes', 0)}")
    print(f"  Commented Code Blocks: {summary.get('commented_code_blocks', 0)}")
    print(f"  Languages Analyzed: {', '.join(summary.get('languages_analyzed', []))}")
    
    for lang, analysis in result.get('analysis', {}).items():
        print(f"\n" + "-" * 40)
        print(f"{lang.upper()} ANALYSIS")
        print("-" * 40)
        
        if analysis.get('potentially_unused_functions'):
            print("\n  Potentially Unused Functions:")
            for func in analysis['potentially_unused_functions'][:15]:
                print(f"    - {func['name']} ({func['file']}:{func['line']})")
            if len(analysis['potentially_unused_functions']) > 15:
                print(f"    ... and {len(analysis['potentially_unused_functions']) - 15} more")
        
        if analysis.get('potentially_unused_classes'):
            print("\n  Potentially Unused Classes:")
            for cls in analysis['potentially_unused_classes'][:10]:
                print(f"    - {cls['name']} ({cls['file']}:{cls['line']})")
            if len(analysis['potentially_unused_classes']) > 10:
                print(f"    ... and {len(analysis['potentially_unused_classes']) - 10} more")
        
        if analysis.get('commented_code_blocks'):
            print("\n  Commented Code Blocks:")
            for block in analysis['commented_code_blocks'][:10]:
                print(f"    - {block['file']}:{block['start_line']} ({block['lines']} lines)")
    
    print("\n" + "-" * 40)
    print("EXTERNAL TOOLS")
    print("-" * 40)
    for tool, info in result.get('external_tools', {}).items():
        if info.get('available'):
            print(f"  {tool}: Available")
        else:
            print(f"  {tool}: {info.get('message', 'Not available')}")
    
    print("\n" + "-" * 40)
    print("RECOMMENDATIONS")
    print("-" * 40)
    print("  1. Review each potentially unused item before removing")
    print("  2. Check for dynamic usage (reflection, getattr, eval)")
    print("  3. Check if functions are called from external packages")
    print("  4. Remove commented-out code (use version control instead)")
    print("  5. Run tests after removing any code")
    
    print("\n" + "=" * 60)


def main():
    parser = argparse.ArgumentParser(
        description='Find dead code in a repository',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    python find_dead_code.py /path/to/repo
    python find_dead_code.py . --language python
    python find_dead_code.py . --json
        """
    )
    parser.add_argument('repo_path', help='Path to the repository to analyze')
    parser.add_argument('--language', '-l', choices=['python', 'javascript', 'typescript', 'js', 'ts'],
                        help='Analyze only specific language')
    parser.add_argument('--json', action='store_true', help='Output as JSON')
    
    args = parser.parse_args()
    
    result = find_dead_code(args.repo_path, args.language)
    
    if 'error' in result:
        print(f"Error: {result['error']}", file=sys.stderr)
        sys.exit(1)
    
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print_report(result)


if __name__ == '__main__':
    main()
