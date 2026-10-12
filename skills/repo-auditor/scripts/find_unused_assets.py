#!/usr/bin/env python3
"""
Find Unused Assets Script

Identifies orphaned files, unused images, stale configurations, and unused dependencies.

Usage:
    python find_unused_assets.py <repo-path> [--json]

Examples:
    python find_unused_assets.py /path/to/repo
    python find_unused_assets.py . --json
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
    '.next', '.nuxt', 'coverage', '.pytest_cache', '.mypy_cache'
}

# Image file extensions
IMAGE_EXTENSIONS = {'.png', '.jpg', '.jpeg', '.gif', '.svg', '.ico', '.webp', '.bmp', '.tiff'}

# Font file extensions
FONT_EXTENSIONS = {'.woff', '.woff2', '.ttf', '.otf', '.eot'}

# Static asset extensions
STATIC_EXTENSIONS = IMAGE_EXTENSIONS | FONT_EXTENSIONS | {'.pdf', '.mp3', '.mp4', '.webm', '.ogg'}

# Source file extensions to search for references
SOURCE_EXTENSIONS = {
    '.py', '.js', '.jsx', '.ts', '.tsx', '.vue', '.svelte',
    '.html', '.htm', '.css', '.scss', '.sass', '.less',
    '.md', '.mdx', '.json', '.yaml', '.yml', '.xml'
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


def find_all_files(repo_path, extensions=None):
    """Find all files in the repository with optional extension filter."""
    files = []
    for root, dirs, filenames in os.walk(repo_path):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS]
        for filename in filenames:
            if extensions is None or any(filename.lower().endswith(ext) for ext in extensions):
                files.append(os.path.join(root, filename))
    return files


def find_static_assets(repo_path):
    """Find all static assets (images, fonts, etc.) in the repository."""
    return find_all_files(repo_path, STATIC_EXTENSIONS)


def find_source_files(repo_path):
    """Find all source files in the repository."""
    return find_all_files(repo_path, SOURCE_EXTENSIONS)


def is_asset_referenced(asset_path, repo_path, source_files):
    """Check if an asset is referenced in any source file."""
    asset_name = os.path.basename(asset_path)
    asset_rel_path = os.path.relpath(asset_path, repo_path)
    
    # Patterns to search for
    patterns = [
        asset_name,  # Just the filename
        asset_rel_path,  # Relative path
        asset_rel_path.replace('\\', '/'),  # Unix-style path
    ]
    
    # Also check without extension for some cases
    name_without_ext = os.path.splitext(asset_name)[0]
    if len(name_without_ext) > 3:  # Avoid false positives with short names
        patterns.append(name_without_ext)
    
    for source_file in source_files:
        try:
            with open(source_file, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
            
            for pattern in patterns:
                if pattern in content:
                    return True
        except Exception:
            pass
    
    return False


def find_unused_images(repo_path):
    """Find images that are not referenced in source files."""
    unused = []
    
    image_files = find_all_files(repo_path, IMAGE_EXTENSIONS)
    source_files = find_source_files(repo_path)
    
    for image_path in image_files:
        if not is_asset_referenced(image_path, repo_path, source_files):
            unused.append({
                'path': os.path.relpath(image_path, repo_path),
                'size_bytes': os.path.getsize(image_path),
                'type': 'image'
            })
    
    return unused


def find_unused_fonts(repo_path):
    """Find fonts that are not referenced in source files."""
    unused = []
    
    font_files = find_all_files(repo_path, FONT_EXTENSIONS)
    source_files = find_source_files(repo_path)
    
    for font_path in font_files:
        if not is_asset_referenced(font_path, repo_path, source_files):
            unused.append({
                'path': os.path.relpath(font_path, repo_path),
                'size_bytes': os.path.getsize(font_path),
                'type': 'font'
            })
    
    return unused


def check_npm_unused_deps(repo_path):
    """Check for unused npm dependencies using depcheck."""
    package_json = os.path.join(repo_path, 'package.json')
    if not os.path.exists(package_json):
        return None
    
    # Try running depcheck
    result = run_command('npx depcheck --json 2>/dev/null', cwd=repo_path)
    
    if result['stdout'].strip():
        try:
            data = json.loads(result['stdout'])
            return {
                'unused_dependencies': data.get('dependencies', []),
                'unused_devDependencies': data.get('devDependencies', []),
                'missing_dependencies': data.get('missing', {}),
                'tool': 'depcheck'
            }
        except json.JSONDecodeError:
            pass
    
    # Fallback: manual analysis
    try:
        with open(package_json, 'r') as f:
            pkg_data = json.load(f)
        
        deps = list(pkg_data.get('dependencies', {}).keys())
        dev_deps = list(pkg_data.get('devDependencies', {}).keys())
        
        # Search for usage in source files
        source_files = find_source_files(repo_path)
        unused_deps = []
        unused_dev_deps = []
        
        for dep in deps:
            found = False
            for source_file in source_files:
                try:
                    with open(source_file, 'r', encoding='utf-8', errors='ignore') as f:
                        content = f.read()
                    # Check for import/require statements
                    if re.search(rf"['\"]({re.escape(dep)})['\"/]", content):
                        found = True
                        break
                    if re.search(rf"from\s+['\"]({re.escape(dep)})", content):
                        found = True
                        break
                    if re.search(rf"require\(['\"]({re.escape(dep)})", content):
                        found = True
                        break
                except Exception:
                    pass
            
            if not found:
                unused_deps.append(dep)
        
        return {
            'unused_dependencies': unused_deps[:20],  # Limit to avoid false positives
            'unused_devDependencies': [],  # Skip dev deps for manual analysis
            'tool': 'manual_analysis',
            'note': 'Manual analysis may have false positives. Consider running npx depcheck for accurate results.'
        }
    except Exception as e:
        return {'error': str(e)}


def check_pip_unused_deps(repo_path):
    """Check for unused pip dependencies."""
    requirements_path = os.path.join(repo_path, 'requirements.txt')
    if not os.path.exists(requirements_path):
        return None
    
    try:
        with open(requirements_path, 'r') as f:
            lines = f.readlines()
        
        deps = []
        for line in lines:
            line = line.strip()
            if not line or line.startswith('#') or line.startswith('-'):
                continue
            # Extract package name
            match = re.match(r'^([a-zA-Z0-9_-]+)', line)
            if match:
                deps.append(match.group(1))
        
        # Search for usage in Python files
        python_files = find_all_files(repo_path, {'.py'})
        unused_deps = []
        
        for dep in deps:
            found = False
            # Normalize package name for import (e.g., python-dateutil -> dateutil)
            import_name = dep.replace('-', '_').lower()
            
            for py_file in python_files:
                try:
                    with open(py_file, 'r', encoding='utf-8', errors='ignore') as f:
                        content = f.read().lower()
                    
                    # Check for import statements
                    if re.search(rf"^import\s+{re.escape(import_name)}", content, re.MULTILINE):
                        found = True
                        break
                    if re.search(rf"^from\s+{re.escape(import_name)}", content, re.MULTILINE):
                        found = True
                        break
                except Exception:
                    pass
            
            if not found:
                unused_deps.append(dep)
        
        return {
            'unused_dependencies': unused_deps,
            'tool': 'manual_analysis',
            'note': 'Manual analysis may have false positives. Some packages are used indirectly.'
        }
    except Exception as e:
        return {'error': str(e)}


def find_stale_branches(repo_path):
    """Find stale git branches."""
    if not os.path.exists(os.path.join(repo_path, '.git')):
        return None
    
    stale_branches = []
    
    # Find merged branches
    result = run_command('git branch --merged main 2>/dev/null || git branch --merged master 2>/dev/null', cwd=repo_path)
    if result['stdout']:
        for branch in result['stdout'].strip().split('\n'):
            branch = branch.strip().lstrip('* ')
            if branch and branch not in ('main', 'master', 'develop', 'dev'):
                stale_branches.append({
                    'name': branch,
                    'status': 'merged'
                })
    
    # Find old branches (no commits in 90 days)
    result = run_command(
        'git for-each-ref --sort=-committerdate refs/heads/ --format="%(refname:short) %(committerdate:unix)" 2>/dev/null',
        cwd=repo_path
    )
    if result['stdout']:
        import time
        ninety_days_ago = time.time() - (90 * 24 * 60 * 60)
        
        for line in result['stdout'].strip().split('\n'):
            parts = line.strip().split()
            if len(parts) >= 2:
                branch_name = parts[0]
                try:
                    commit_time = int(parts[1])
                    if commit_time < ninety_days_ago and branch_name not in ('main', 'master'):
                        # Check if not already in stale list
                        if not any(b['name'] == branch_name for b in stale_branches):
                            stale_branches.append({
                                'name': branch_name,
                                'status': 'stale',
                                'days_old': int((time.time() - commit_time) / (24 * 60 * 60))
                            })
                except ValueError:
                    pass
    
    return stale_branches


def find_unused_env_vars(repo_path):
    """Find environment variables defined but not used."""
    env_file = os.path.join(repo_path, '.env.example')
    if not os.path.exists(env_file):
        env_file = os.path.join(repo_path, '.env.sample')
    if not os.path.exists(env_file):
        env_file = os.path.join(repo_path, '.env.template')
    if not os.path.exists(env_file):
        return None
    
    try:
        with open(env_file, 'r') as f:
            lines = f.readlines()
        
        env_vars = []
        for line in lines:
            line = line.strip()
            if not line or line.startswith('#'):
                continue
            match = re.match(r'^([A-Z_][A-Z0-9_]*)=', line)
            if match:
                env_vars.append(match.group(1))
        
        # Search for usage in source files
        source_files = find_source_files(repo_path)
        unused_vars = []
        
        for var in env_vars:
            found = False
            for source_file in source_files:
                try:
                    with open(source_file, 'r', encoding='utf-8', errors='ignore') as f:
                        content = f.read()
                    
                    # Check for various ways env vars are accessed
                    patterns = [
                        rf"process\.env\.{var}",
                        rf"os\.environ\[['\"]?{var}",
                        rf"os\.getenv\(['\"]?{var}",
                        rf"env\(['\"]?{var}",
                        rf"\${{{var}}}",
                        rf"\${var}",
                    ]
                    
                    for pattern in patterns:
                        if re.search(pattern, content):
                            found = True
                            break
                    
                    if found:
                        break
                except Exception:
                    pass
            
            if not found:
                unused_vars.append(var)
        
        return {
            'env_file': os.path.relpath(env_file, repo_path),
            'total_vars': len(env_vars),
            'unused_vars': unused_vars
        }
    except Exception as e:
        return {'error': str(e)}


def find_orphaned_configs(repo_path):
    """Find configuration files for tools that aren't being used."""
    orphaned = []
    
    # Config files and their associated tools/files
    config_checks = [
        ('.babelrc', ['package.json'], 'babel'),
        ('babel.config.js', ['package.json'], 'babel'),
        ('.eslintrc', ['package.json'], 'eslint'),
        ('.eslintrc.js', ['package.json'], 'eslint'),
        ('.prettierrc', ['package.json'], 'prettier'),
        ('jest.config.js', ['package.json'], 'jest'),
        ('webpack.config.js', ['package.json'], 'webpack'),
        ('tsconfig.json', ['.ts', '.tsx'], 'typescript'),
        ('.pylintrc', ['.py'], 'pylint'),
        ('mypy.ini', ['.py'], 'mypy'),
        ('.flake8', ['.py'], 'flake8'),
        ('pytest.ini', ['.py'], 'pytest'),
        ('setup.cfg', ['setup.py', 'pyproject.toml'], 'setuptools'),
        ('.rubocop.yml', ['.rb'], 'rubocop'),
        ('Gemfile', ['.rb'], 'bundler'),
    ]
    
    for config_file, check_for, tool_name in config_checks:
        config_path = os.path.join(repo_path, config_file)
        if os.path.exists(config_path):
            # Check if the associated files/tools exist
            has_associated = False
            for check in check_for:
                if check.startswith('.'):
                    # It's an extension, check for files with that extension
                    if find_all_files(repo_path, {check}):
                        has_associated = True
                        break
                else:
                    # It's a file, check if it exists
                    if os.path.exists(os.path.join(repo_path, check)):
                        has_associated = True
                        break
            
            if not has_associated:
                orphaned.append({
                    'config': config_file,
                    'tool': tool_name,
                    'reason': f'No {check_for} files found'
                })
    
    return orphaned


def find_unused_assets(repo_path):
    """Perform full unused asset analysis on a repository."""
    if not os.path.isdir(repo_path):
        return {'error': f'Path does not exist or is not a directory: {repo_path}'}
    
    result = {
        'repository': os.path.abspath(repo_path),
        'unused_images': find_unused_images(repo_path),
        'unused_fonts': find_unused_fonts(repo_path),
        'npm_unused': check_npm_unused_deps(repo_path),
        'pip_unused': check_pip_unused_deps(repo_path),
        'stale_branches': find_stale_branches(repo_path),
        'unused_env_vars': find_unused_env_vars(repo_path),
        'orphaned_configs': find_orphaned_configs(repo_path)
    }
    
    # Calculate total wasted space
    total_wasted_bytes = 0
    for img in result['unused_images']:
        total_wasted_bytes += img.get('size_bytes', 0)
    for font in result['unused_fonts']:
        total_wasted_bytes += font.get('size_bytes', 0)
    
    # Summary
    result['summary'] = {
        'unused_images': len(result['unused_images']),
        'unused_fonts': len(result['unused_fonts']),
        'unused_npm_deps': len(result.get('npm_unused', {}).get('unused_dependencies', [])) if result.get('npm_unused') else 0,
        'unused_pip_deps': len(result.get('pip_unused', {}).get('unused_dependencies', [])) if result.get('pip_unused') else 0,
        'stale_branches': len(result['stale_branches']) if result['stale_branches'] else 0,
        'unused_env_vars': len(result.get('unused_env_vars', {}).get('unused_vars', [])) if result.get('unused_env_vars') else 0,
        'orphaned_configs': len(result['orphaned_configs']),
        'wasted_space_bytes': total_wasted_bytes,
        'wasted_space_mb': round(total_wasted_bytes / (1024 * 1024), 2)
    }
    
    return result


def print_report(result):
    """Print a human-readable report."""
    print("=" * 60)
    print("UNUSED ASSETS REPORT")
    print("=" * 60)
    print(f"\nRepository: {result['repository']}")
    
    print("\n" + "-" * 40)
    print("SUMMARY")
    print("-" * 40)
    summary = result.get('summary', {})
    print(f"  Unused Images: {summary.get('unused_images', 0)}")
    print(f"  Unused Fonts: {summary.get('unused_fonts', 0)}")
    print(f"  Unused npm Dependencies: {summary.get('unused_npm_deps', 0)}")
    print(f"  Unused pip Dependencies: {summary.get('unused_pip_deps', 0)}")
    print(f"  Stale Git Branches: {summary.get('stale_branches', 0)}")
    print(f"  Unused Environment Variables: {summary.get('unused_env_vars', 0)}")
    print(f"  Orphaned Config Files: {summary.get('orphaned_configs', 0)}")
    print(f"  Wasted Space: {summary.get('wasted_space_mb', 0)} MB")
    
    if result['unused_images']:
        print("\n" + "-" * 40)
        print("UNUSED IMAGES")
        print("-" * 40)
        for img in result['unused_images'][:15]:
            size_kb = img['size_bytes'] / 1024
            print(f"  {img['path']} ({size_kb:.1f} KB)")
        if len(result['unused_images']) > 15:
            print(f"  ... and {len(result['unused_images']) - 15} more")
    
    if result['unused_fonts']:
        print("\n" + "-" * 40)
        print("UNUSED FONTS")
        print("-" * 40)
        for font in result['unused_fonts'][:10]:
            size_kb = font['size_bytes'] / 1024
            print(f"  {font['path']} ({size_kb:.1f} KB)")
    
    if result.get('npm_unused') and result['npm_unused'].get('unused_dependencies'):
        print("\n" + "-" * 40)
        print("UNUSED NPM DEPENDENCIES")
        print("-" * 40)
        for dep in result['npm_unused']['unused_dependencies'][:15]:
            print(f"  {dep}")
        if result['npm_unused'].get('note'):
            print(f"\n  Note: {result['npm_unused']['note']}")
    
    if result.get('pip_unused') and result['pip_unused'].get('unused_dependencies'):
        print("\n" + "-" * 40)
        print("UNUSED PIP DEPENDENCIES")
        print("-" * 40)
        for dep in result['pip_unused']['unused_dependencies'][:15]:
            print(f"  {dep}")
        if result['pip_unused'].get('note'):
            print(f"\n  Note: {result['pip_unused']['note']}")
    
    if result.get('stale_branches'):
        print("\n" + "-" * 40)
        print("STALE GIT BRANCHES")
        print("-" * 40)
        for branch in result['stale_branches'][:10]:
            status = branch['status']
            if 'days_old' in branch:
                print(f"  {branch['name']} ({status}, {branch['days_old']} days old)")
            else:
                print(f"  {branch['name']} ({status})")
    
    if result.get('unused_env_vars') and result['unused_env_vars'].get('unused_vars'):
        print("\n" + "-" * 40)
        print("UNUSED ENVIRONMENT VARIABLES")
        print("-" * 40)
        print(f"  From: {result['unused_env_vars']['env_file']}")
        for var in result['unused_env_vars']['unused_vars'][:10]:
            print(f"  {var}")
    
    if result.get('orphaned_configs'):
        print("\n" + "-" * 40)
        print("ORPHANED CONFIG FILES")
        print("-" * 40)
        for config in result['orphaned_configs']:
            print(f"  {config['config']} ({config['tool']}) - {config['reason']}")
    
    print("\n" + "-" * 40)
    print("RECOMMENDATIONS")
    print("-" * 40)
    print("  1. Review unused images before deleting (may be loaded dynamically)")
    print("  2. Run 'npm uninstall <pkg>' for unused npm dependencies")
    print("  3. Delete merged branches: git branch -d <branch>")
    print("  4. Remove orphaned config files if tools are not used")
    print("  5. Clean up unused environment variables from templates")
    
    print("\n" + "=" * 60)


def main():
    parser = argparse.ArgumentParser(
        description='Find unused assets in a repository',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    python find_unused_assets.py /path/to/repo
    python find_unused_assets.py . --json
        """
    )
    parser.add_argument('repo_path', help='Path to the repository to analyze')
    parser.add_argument('--json', action='store_true', help='Output as JSON')
    
    args = parser.parse_args()
    
    result = find_unused_assets(args.repo_path)
    
    if 'error' in result:
        print(f"Error: {result['error']}", file=sys.stderr)
        sys.exit(1)
    
    if args.json:
        print(json.dumps(result, indent=2, default=str))
    else:
        print_report(result)


if __name__ == '__main__':
    main()
