#!/usr/bin/env python3
"""
Analyze Tech Stack Script

Detects languages, frameworks, build tools, and infrastructure in a repository.

Usage:
    python analyze_tech_stack.py <repo-path> [--json]

Examples:
    python analyze_tech_stack.py /path/to/repo
    python analyze_tech_stack.py . --json
"""

import argparse
import json
import os
import sys
from collections import defaultdict
from pathlib import Path


# File extension to language mapping
EXTENSION_LANGUAGE_MAP = {
    '.py': 'Python',
    '.js': 'JavaScript',
    '.ts': 'TypeScript',
    '.tsx': 'TypeScript (React)',
    '.jsx': 'JavaScript (React)',
    '.go': 'Go',
    '.rs': 'Rust',
    '.java': 'Java',
    '.kt': 'Kotlin',
    '.scala': 'Scala',
    '.rb': 'Ruby',
    '.php': 'PHP',
    '.cs': 'C#',
    '.cpp': 'C++',
    '.c': 'C',
    '.h': 'C/C++ Header',
    '.swift': 'Swift',
    '.m': 'Objective-C',
    '.r': 'R',
    '.R': 'R',
    '.lua': 'Lua',
    '.pl': 'Perl',
    '.sh': 'Shell',
    '.bash': 'Bash',
    '.zsh': 'Zsh',
    '.ps1': 'PowerShell',
    '.sql': 'SQL',
    '.html': 'HTML',
    '.css': 'CSS',
    '.scss': 'SCSS',
    '.sass': 'Sass',
    '.less': 'Less',
    '.vue': 'Vue',
    '.svelte': 'Svelte',
}

# Package manager files and their ecosystems
PACKAGE_MANAGERS = {
    'package.json': {'ecosystem': 'Node.js/npm', 'type': 'package_manager'},
    'package-lock.json': {'ecosystem': 'npm', 'type': 'lockfile'},
    'yarn.lock': {'ecosystem': 'Yarn', 'type': 'lockfile'},
    'pnpm-lock.yaml': {'ecosystem': 'pnpm', 'type': 'lockfile'},
    'requirements.txt': {'ecosystem': 'Python/pip', 'type': 'package_manager'},
    'setup.py': {'ecosystem': 'Python/setuptools', 'type': 'package_manager'},
    'pyproject.toml': {'ecosystem': 'Python/Poetry/PEP517', 'type': 'package_manager'},
    'Pipfile': {'ecosystem': 'Python/Pipenv', 'type': 'package_manager'},
    'Pipfile.lock': {'ecosystem': 'Pipenv', 'type': 'lockfile'},
    'poetry.lock': {'ecosystem': 'Poetry', 'type': 'lockfile'},
    'go.mod': {'ecosystem': 'Go Modules', 'type': 'package_manager'},
    'go.sum': {'ecosystem': 'Go Modules', 'type': 'lockfile'},
    'Cargo.toml': {'ecosystem': 'Rust/Cargo', 'type': 'package_manager'},
    'Cargo.lock': {'ecosystem': 'Cargo', 'type': 'lockfile'},
    'pom.xml': {'ecosystem': 'Java/Maven', 'type': 'package_manager'},
    'build.gradle': {'ecosystem': 'Java/Gradle', 'type': 'package_manager'},
    'build.gradle.kts': {'ecosystem': 'Kotlin/Gradle', 'type': 'package_manager'},
    'Gemfile': {'ecosystem': 'Ruby/Bundler', 'type': 'package_manager'},
    'Gemfile.lock': {'ecosystem': 'Bundler', 'type': 'lockfile'},
    'composer.json': {'ecosystem': 'PHP/Composer', 'type': 'package_manager'},
    'composer.lock': {'ecosystem': 'Composer', 'type': 'lockfile'},
}

# CI/CD configuration files
CI_CD_CONFIGS = {
    '.github/workflows': 'GitHub Actions',
    '.gitlab-ci.yml': 'GitLab CI',
    'Jenkinsfile': 'Jenkins',
    '.circleci/config.yml': 'CircleCI',
    '.travis.yml': 'Travis CI',
    'azure-pipelines.yml': 'Azure Pipelines',
    'bitbucket-pipelines.yml': 'Bitbucket Pipelines',
    '.drone.yml': 'Drone CI',
    'cloudbuild.yaml': 'Google Cloud Build',
    'buildspec.yml': 'AWS CodeBuild',
}

# Infrastructure files
INFRASTRUCTURE_FILES = {
    'Dockerfile': 'Docker',
    'docker-compose.yml': 'Docker Compose',
    'docker-compose.yaml': 'Docker Compose',
    'kubernetes': 'Kubernetes',
    'k8s': 'Kubernetes',
    'helm': 'Helm',
    'Chart.yaml': 'Helm Chart',
    'terraform': 'Terraform',
    'serverless.yml': 'Serverless Framework',
    'serverless.yaml': 'Serverless Framework',
    'sam.yaml': 'AWS SAM',
    'template.yaml': 'AWS SAM/CloudFormation',
    'pulumi': 'Pulumi',
    'Pulumi.yaml': 'Pulumi',
    'ansible': 'Ansible',
    'playbook.yml': 'Ansible',
}

# Build tool configurations
BUILD_TOOLS = {
    'webpack.config.js': 'Webpack',
    'webpack.config.ts': 'Webpack',
    'vite.config.js': 'Vite',
    'vite.config.ts': 'Vite',
    'rollup.config.js': 'Rollup',
    'esbuild.config.js': 'esbuild',
    'tsconfig.json': 'TypeScript Compiler',
    'babel.config.js': 'Babel',
    '.babelrc': 'Babel',
    'Makefile': 'Make',
    'Taskfile.yml': 'Task',
    'justfile': 'Just',
    'Rakefile': 'Rake',
    'gulpfile.js': 'Gulp',
    'Gruntfile.js': 'Grunt',
}

# Code quality tools
CODE_QUALITY_TOOLS = {
    '.eslintrc': 'ESLint',
    '.eslintrc.js': 'ESLint',
    '.eslintrc.json': 'ESLint',
    'eslint.config.js': 'ESLint',
    '.prettierrc': 'Prettier',
    '.prettierrc.js': 'Prettier',
    'prettier.config.js': 'Prettier',
    '.pylintrc': 'Pylint',
    'pylintrc': 'Pylint',
    '.flake8': 'Flake8',
    'mypy.ini': 'mypy',
    '.mypy.ini': 'mypy',
    'pyrightconfig.json': 'Pyright',
    '.rubocop.yml': 'RuboCop',
    'golangci.yml': 'golangci-lint',
    '.golangci.yml': 'golangci-lint',
    'rustfmt.toml': 'rustfmt',
    '.editorconfig': 'EditorConfig',
    'sonar-project.properties': 'SonarQube',
}

# Framework detection patterns (check in package.json, requirements.txt, etc.)
FRAMEWORK_PATTERNS = {
    'react': 'React',
    'vue': 'Vue.js',
    'angular': 'Angular',
    'svelte': 'Svelte',
    'next': 'Next.js',
    'nuxt': 'Nuxt.js',
    'gatsby': 'Gatsby',
    'express': 'Express.js',
    'fastify': 'Fastify',
    'koa': 'Koa',
    'nestjs': 'NestJS',
    'django': 'Django',
    'flask': 'Flask',
    'fastapi': 'FastAPI',
    'tornado': 'Tornado',
    'pyramid': 'Pyramid',
    'rails': 'Ruby on Rails',
    'sinatra': 'Sinatra',
    'spring': 'Spring',
    'spring-boot': 'Spring Boot',
    'laravel': 'Laravel',
    'symfony': 'Symfony',
    'gin': 'Gin',
    'echo': 'Echo',
    'fiber': 'Fiber',
    'actix': 'Actix',
    'rocket': 'Rocket',
    'axum': 'Axum',
    'flutter': 'Flutter',
    'react-native': 'React Native',
    'electron': 'Electron',
    'tauri': 'Tauri',
}


def count_files_by_extension(repo_path):
    """Count files by extension to determine primary languages."""
    extension_counts = defaultdict(int)
    
    for root, dirs, files in os.walk(repo_path):
        # Skip common non-source directories
        dirs[:] = [d for d in dirs if d not in [
            'node_modules', 'venv', '.venv', 'env', '.env',
            '__pycache__', '.git', '.svn', 'vendor', 'target',
            'build', 'dist', 'out', '.next', '.nuxt', 'coverage'
        ]]
        
        for file in files:
            ext = os.path.splitext(file)[1].lower()
            if ext:
                extension_counts[ext] += 1
    
    return dict(extension_counts)


def detect_languages(extension_counts):
    """Detect languages based on file extensions."""
    languages = {}
    
    for ext, count in extension_counts.items():
        if ext in EXTENSION_LANGUAGE_MAP:
            lang = EXTENSION_LANGUAGE_MAP[ext]
            if lang in languages:
                languages[lang] += count
            else:
                languages[lang] = count
    
    # Sort by count
    return dict(sorted(languages.items(), key=lambda x: x[1], reverse=True))


def detect_package_managers(repo_path):
    """Detect package managers and dependency files."""
    found = []
    
    for filename, info in PACKAGE_MANAGERS.items():
        filepath = os.path.join(repo_path, filename)
        if os.path.exists(filepath):
            found.append({
                'file': filename,
                'ecosystem': info['ecosystem'],
                'type': info['type']
            })
    
    return found


def detect_ci_cd(repo_path):
    """Detect CI/CD configurations."""
    found = []
    
    for path, name in CI_CD_CONFIGS.items():
        full_path = os.path.join(repo_path, path)
        if os.path.exists(full_path):
            found.append({'path': path, 'platform': name})
    
    return found


def detect_infrastructure(repo_path):
    """Detect infrastructure and deployment configurations."""
    found = []
    
    for filename, tech in INFRASTRUCTURE_FILES.items():
        # Check for files
        filepath = os.path.join(repo_path, filename)
        if os.path.exists(filepath):
            found.append({'path': filename, 'technology': tech})
        
        # Check for directories
        if os.path.isdir(filepath):
            found.append({'path': filename, 'technology': tech})
    
    # Check for .tf files (Terraform)
    for root, dirs, files in os.walk(repo_path):
        dirs[:] = [d for d in dirs if d not in ['node_modules', '.git', 'vendor']]
        for file in files:
            if file.endswith('.tf'):
                found.append({'path': os.path.relpath(os.path.join(root, file), repo_path), 'technology': 'Terraform'})
                break
        if any(f.get('technology') == 'Terraform' for f in found):
            break
    
    return found


def detect_build_tools(repo_path):
    """Detect build tools and configurations."""
    found = []
    
    for filename, tool in BUILD_TOOLS.items():
        filepath = os.path.join(repo_path, filename)
        if os.path.exists(filepath):
            found.append({'file': filename, 'tool': tool})
    
    return found


def detect_code_quality_tools(repo_path):
    """Detect code quality and linting tools."""
    found = []
    
    for filename, tool in CODE_QUALITY_TOOLS.items():
        filepath = os.path.join(repo_path, filename)
        if os.path.exists(filepath):
            found.append({'file': filename, 'tool': tool})
    
    return found


def detect_frameworks(repo_path):
    """Detect frameworks from dependency files."""
    found = []
    
    # Check package.json
    package_json_path = os.path.join(repo_path, 'package.json')
    if os.path.exists(package_json_path):
        try:
            with open(package_json_path, 'r') as f:
                data = json.load(f)
                deps = {}
                deps.update(data.get('dependencies', {}))
                deps.update(data.get('devDependencies', {}))
                
                for dep_name in deps.keys():
                    dep_lower = dep_name.lower()
                    for pattern, framework in FRAMEWORK_PATTERNS.items():
                        if pattern in dep_lower:
                            if framework not in [f['framework'] for f in found]:
                                found.append({'framework': framework, 'source': 'package.json'})
        except (json.JSONDecodeError, IOError):
            pass
    
    # Check requirements.txt
    requirements_path = os.path.join(repo_path, 'requirements.txt')
    if os.path.exists(requirements_path):
        try:
            with open(requirements_path, 'r') as f:
                content = f.read().lower()
                for pattern, framework in FRAMEWORK_PATTERNS.items():
                    if pattern in content:
                        if framework not in [f['framework'] for f in found]:
                            found.append({'framework': framework, 'source': 'requirements.txt'})
        except IOError:
            pass
    
    # Check pyproject.toml
    pyproject_path = os.path.join(repo_path, 'pyproject.toml')
    if os.path.exists(pyproject_path):
        try:
            with open(pyproject_path, 'r') as f:
                content = f.read().lower()
                for pattern, framework in FRAMEWORK_PATTERNS.items():
                    if pattern in content:
                        if framework not in [f['framework'] for f in found]:
                            found.append({'framework': framework, 'source': 'pyproject.toml'})
        except IOError:
            pass
    
    # Check go.mod
    gomod_path = os.path.join(repo_path, 'go.mod')
    if os.path.exists(gomod_path):
        try:
            with open(gomod_path, 'r') as f:
                content = f.read().lower()
                for pattern, framework in FRAMEWORK_PATTERNS.items():
                    if pattern in content:
                        if framework not in [f['framework'] for f in found]:
                            found.append({'framework': framework, 'source': 'go.mod'})
        except IOError:
            pass
    
    # Check Cargo.toml
    cargo_path = os.path.join(repo_path, 'Cargo.toml')
    if os.path.exists(cargo_path):
        try:
            with open(cargo_path, 'r') as f:
                content = f.read().lower()
                for pattern, framework in FRAMEWORK_PATTERNS.items():
                    if pattern in content:
                        if framework not in [f['framework'] for f in found]:
                            found.append({'framework': framework, 'source': 'Cargo.toml'})
        except IOError:
            pass
    
    return found


def analyze_repo(repo_path):
    """Perform full tech stack analysis on a repository."""
    if not os.path.isdir(repo_path):
        return {'error': f'Path does not exist or is not a directory: {repo_path}'}
    
    extension_counts = count_files_by_extension(repo_path)
    languages = detect_languages(extension_counts)
    
    result = {
        'repository': os.path.abspath(repo_path),
        'languages': languages,
        'primary_language': list(languages.keys())[0] if languages else None,
        'package_managers': detect_package_managers(repo_path),
        'frameworks': detect_frameworks(repo_path),
        'build_tools': detect_build_tools(repo_path),
        'ci_cd': detect_ci_cd(repo_path),
        'infrastructure': detect_infrastructure(repo_path),
        'code_quality_tools': detect_code_quality_tools(repo_path),
        'file_extension_counts': extension_counts,
    }
    
    return result


def print_report(result):
    """Print a human-readable report."""
    print("=" * 60)
    print("TECH STACK ANALYSIS REPORT")
    print("=" * 60)
    print(f"\nRepository: {result['repository']}")
    
    print("\n" + "-" * 40)
    print("LANGUAGES")
    print("-" * 40)
    if result['languages']:
        for lang, count in result['languages'].items():
            print(f"  {lang}: {count} files")
        print(f"\n  Primary Language: {result['primary_language']}")
    else:
        print("  No source files detected")
    
    print("\n" + "-" * 40)
    print("PACKAGE MANAGERS")
    print("-" * 40)
    if result['package_managers']:
        for pm in result['package_managers']:
            print(f"  {pm['ecosystem']} ({pm['file']})")
    else:
        print("  No package managers detected")
    
    print("\n" + "-" * 40)
    print("FRAMEWORKS")
    print("-" * 40)
    if result['frameworks']:
        for fw in result['frameworks']:
            print(f"  {fw['framework']} (from {fw['source']})")
    else:
        print("  No frameworks detected")
    
    print("\n" + "-" * 40)
    print("BUILD TOOLS")
    print("-" * 40)
    if result['build_tools']:
        for bt in result['build_tools']:
            print(f"  {bt['tool']} ({bt['file']})")
    else:
        print("  No build tools detected")
    
    print("\n" + "-" * 40)
    print("CI/CD")
    print("-" * 40)
    if result['ci_cd']:
        for ci in result['ci_cd']:
            print(f"  {ci['platform']} ({ci['path']})")
    else:
        print("  No CI/CD configurations detected")
    
    print("\n" + "-" * 40)
    print("INFRASTRUCTURE")
    print("-" * 40)
    if result['infrastructure']:
        for infra in result['infrastructure']:
            print(f"  {infra['technology']} ({infra['path']})")
    else:
        print("  No infrastructure configurations detected")
    
    print("\n" + "-" * 40)
    print("CODE QUALITY TOOLS")
    print("-" * 40)
    if result['code_quality_tools']:
        for tool in result['code_quality_tools']:
            print(f"  {tool['tool']} ({tool['file']})")
    else:
        print("  No code quality tools detected")
    
    print("\n" + "=" * 60)


def main():
    parser = argparse.ArgumentParser(
        description='Analyze tech stack of a repository',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
    python analyze_tech_stack.py /path/to/repo
    python analyze_tech_stack.py . --json
        """
    )
    parser.add_argument('repo_path', help='Path to the repository to analyze')
    parser.add_argument('--json', action='store_true', help='Output as JSON')
    
    args = parser.parse_args()
    
    result = analyze_repo(args.repo_path)
    
    if 'error' in result:
        print(f"Error: {result['error']}", file=sys.stderr)
        sys.exit(1)
    
    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print_report(result)


if __name__ == '__main__':
    main()
