#!/usr/bin/env python3
"""
Version Bumper

Analyzes commits since last tag to determine the correct version bump (major/minor/patch) 
based on conventional commits. Handles pre-release versions (alpha, beta, rc) and generates 
version bump commands for various package files.

Input: current version + commit list JSON or git log
Output: recommended new version + bump commands + updated file snippets
"""

import argparse
import json
import re
import sys
from typing import Dict, List, Optional, Tuple, Union
from enum import Enum
from dataclasses import dataclass


class BumpType(Enum):
    """Version bump types."""
    NONE = "none"
    PATCH = "patch"
    MINOR = "minor"  
    MAJOR = "major"


class PreReleaseType(Enum):
    """Pre-release types."""
    ALPHA = "alpha"
    BETA = "beta"
    RC = "rc"


@dataclass
class Version:
    """Semantic version representation."""
    major: int
    minor: int
    patch: int
    prerelease_type: Optional[PreReleaseType] = None
    prerelease_number: Optional[int] = None
    
    @classmethod
    def parse(cls, version_str: str) -> 'Version':
        """Parse version string into Version object."""
        # Remove 'v' prefix if present
        clean_version = version_str.lstrip('v')
        
        # Pattern for semantic versioning with optional pre-release
        pattern = r'^(\d+)\.(\d+)\.(\d+)(?:-(\w+)\.?(\d+)?)?$'
        match = re.match(pattern, clean_version)
        
        if not match:
            raise ValueError(f"Invalid version format: {version_str}")
        
        major, minor, patch = int(match.group(1)), int(match.group(2)), int(match.group(3))
        
        prerelease_type = None
        prerelease_number = None
        
        if match.group(4):  # Pre-release identifier
            prerelease_str = match.group(4).lower()
            try:
                prerelease_type = PreReleaseType(prerelease_str)
            except ValueError:
                # Handle variations like 'alpha1' -> 'alpha'
                if prerelease_str.startswith('alpha'):
                    prerelease_type = PreReleaseType.ALPHA
                elif prerelease_str.startswith('beta'):
                    prerelease_type = PreReleaseType.BETA
                elif prerelease_str.startswith('rc'):
                    prerelease_type = PreReleaseType.RC
                else:
                    raise ValueError(f"Unknown pre-release type: {prerelease_str}")
            
            if match.group(5):
                prerelease_number = int(match.group(5))
            else:
                # Extract number from combined string like 'alpha1'
                number_match = re.search(r'(\d+)$', prerelease_str)
                if number_match:
                    prerelease_number = int(number_match.group(1))
                else:
                    prerelease_number = 1  # Default to 1
        
        return cls(major, minor, patch, prerelease_type, prerelease_number)
    
    def to_string(self, include_v_prefix: bool = False) -> str:
        """Convert version to string representation."""
        base = f"{self.major}.{self.minor}.{self.patch}"
        
        if self.prerelease_type:
            if self.prerelease_number is not None:
                base += f"-{self.prerelease_type.value}.{self.prerelease_number}"
            else:
                base += f"-{self.prerelease_type.value}"
        
        return f"v{base}" if include_v_prefix else base
    
    def bump(self, bump_type: BumpType, prerelease_type: Optional[PreReleaseType] = None) -> 'Version':
        """Create new version with specified bump."""
        if bump_type == BumpType.NONE:
            return Version(self.major, self.minor, self.patch, self.prerelease_type, self.prerelease_number)
        
        new_major = self.major
        new_minor = self.minor  
        new_patch = self.patch
        new_prerelease_type = None
        new_prerelease_number = None
        
        # Handle pre-release versions
        if prerelease_type:
            if bump_type == BumpType.MAJOR:
                new_major += 1
                new_minor = 0
                new_patch = 0
            elif bump_type == BumpType.MINOR:
                new_minor += 1
                new_patch = 0
            elif bump_type == BumpType.PATCH:
                new_patch += 1
            
            new_prerelease_type = prerelease_type
            new_prerelease_number = 1
        
        # Handle existing pre-release -> next pre-release
        elif self.prerelease_type:
            # If we're already in pre-release, increment or promote
            if prerelease_type is None:
                # Promote to stable release
                # Don't change version numbers, just remove pre-release
                pass
            else:
                # Move to next pre-release type or increment
                if prerelease_type == self.prerelease_type:
                    # Same pre-release type, increment number
                    new_prerelease_type = self.prerelease_type
                    new_prerelease_number = (self.prerelease_number or 0) + 1
                else:
                    # Different pre-release type
                    new_prerelease_type = prerelease_type
                    new_prerelease_number = 1
        
        # Handle stable version bumps
        else:
            if bump_type == BumpType.MAJOR:
                new_major += 1
                new_minor = 0
                new_patch = 0
            elif bump_type == BumpType.MINOR:
                new_minor += 1
                new_patch = 0
            elif bump_type == BumpType.PATCH:
                new_patch += 1
        
        return Version(new_major, new_minor, new_patch, new_prerelease_type, new_prerelease_number)


@dataclass
class ConventionalCommit:
    """Represents a parsed conventional commit for version analysis."""
    type: str
    scope: str
    description: str
    is_breaking: bool
    breaking_description: str
    hash: str = ""
    author: str = ""
    date: str = ""
    
    @classmethod
    def parse_message(cls, message: str, commit_hash: str = "", 
                     author: str = "", date: str = "") -> 'ConventionalCommit':
        """Parse conventional commit message."""
        lines = message.split('\n')
        header = lines[0] if lines else ""
        
        # Parse header: type(scope): description
        header_pattern = r'^(\w+)(\([^)]+\))?(!)?:\s*(.+)$'
        match = re.match(header_pattern, header)
        
        commit_type = "chore"
        scope = ""
        description = header
        is_breaking = False
        breaking_description = ""
        
        if match:
            commit_type = match.group(1).lower()
            scope_match = match.group(2)
            scope = scope_match[1:-1] if scope_match else ""
            is_breaking = bool(match.group(3))  # ! indicates breaking change
            description = match.group(4).strip()
        
        # Check for breaking change in body/footers
        if len(lines) > 1:
            body_text = '\n'.join(lines[1:])
            if 'BREAKING CHANGE:' in body_text:
                is_breaking = True
                breaking_match = re.search(r'BREAKING CHANGE:\s*(.+)', body_text)
                if breaking_match:
                    breaking_description = breaking_match.group(1).strip()
        
        return cls(commit_type, scope, description, is_breaking, breaking_description,
                  commit_hash, author, date)


class VersionBumper:
    """Main version bumping logic."""
    
    def __init__(self):
        self.current_version: Optional[Version] = None
        self.commits: List[ConventionalCommit] = []
        self.custom_rules: Dict[str, BumpType] = {}
        self.ignore_types: List[str] = ['test', 'ci', 'build', 'chore', 'docs', 'style']
        
    def set_current_version(self, version_str: str):
        """Set the current version."""
        self.current_version = Version.parse(version_str)
    
    def add_custom_rule(self, commit_type: str, bump_type: BumpType):
        """Add custom rule for commit type to bump type mapping."""
        self.custom_rules[commit_type] = bump_type
    
    def parse_commits_from_json(self, json_data: Union[str, List[Dict]]):
        """Parse commits from JSON format."""
        if isinstance(json_data, str):
            data = json.loads(json_data)
        else:
            data = json_data
        
        self.commits = []
        for commit_data in data:
            commit = ConventionalCommit.parse_message(
                message=commit_data.get('message', ''),
                commit_hash=commit_data.get('hash', ''),
                author=commit_data.get('author', ''),
                date=commit_data.get('date', '')
            )
            self.commits.append(commit)
    
    def parse_commits_from_git_log(self, git_log_text: str):
        """Parse commits from git log output."""
        lines = git_log_text.strip().split('\n')
        
        if not lines or not lines[0]:
            return
        
        # Simple oneline format (hash message)
        oneline_pattern = r'^([a-f0-9]{7,40})\s+(.+)$'
        
        self.commits = []
        for line in lines:
            line = line.strip()
            if not line:
                continue
                
            match = re.match(oneline_pattern, line)
            if match:
                commit_hash = match.group(1)
                message = match.group(2)
                commit = ConventionalCommit.parse_message(message, commit_hash)
                self.commits.append(commit)
    
    def determine_bump_type(self) -> BumpType:
        """Determine version bump type based on commits."""
        if not self.commits:
            return BumpType.NONE
        
        has_breaking = False
        has_feature = False
        has_fix = False
        
        for commit in self.commits:
            # Check for breaking changes
            if commit.is_breaking:
                has_breaking = True
                continue
            
            # Apply custom rules first
            if commit.type in self.custom_rules:
                bump_type = self.custom_rules[commit.type]
                if bump_type == BumpType.MAJOR:
                    has_breaking = True
                elif bump_type == BumpType.MINOR:
                    has_feature = True
                elif bump_type == BumpType.PATCH:
                    has_fix = True
                continue
            
            # Standard rules
            if commit.type in ['feat', 'add']:
                has_feature = True
            elif commit.type in ['fix', 'security', 'perf', 'bugfix']:
                has_fix = True
            # Ignore types in ignore_types list
        
        # Determine bump type by priority
        if has_breaking:
            return BumpType.MAJOR
        elif has_feature:
            return BumpType.MINOR
        elif has_fix:
            return BumpType.PATCH
        else:
            return BumpType.NONE
    
    def recommend_version(self, prerelease_type: Optional[PreReleaseType] = None) -> Version:
        """Recommend new version based on commits."""
        if not self.current_version:
            raise ValueError("Current version not set")
        
        bump_type = self.determine_bump_type()
        return self.current_version.bump(bump_type, prerelease_type)
    
    def generate_bump_commands(self, new_version: Version) -> Dict[str, List[str]]:
        """Generate version bump commands for different package managers."""
        version_str = new_version.to_string()
        version_with_v = new_version.to_string(include_v_prefix=True)
        
        commands = {
            'npm': [
                f"npm version {version_str} --no-git-tag-version",
                f"# Or manually edit package.json version field to '{version_str}'"
            ],
            'python': [
                f"# Update version in setup.py, __init__.py, or pyproject.toml",
                f"# setup.py: version='{version_str}'",
                f"# pyproject.toml: version = '{version_str}'",
                f"# __init__.py: __version__ = '{version_str}'"
            ],
            'rust': [
                f"# Update Cargo.toml",
                f"# [package]",
                f"# version = '{version_str}'"
            ],
            'git': [
                f"git tag -a {version_with_v} -m 'Release {version_with_v}'",
                f"git push origin {version_with_v}"
            ],
            'docker': [
                f"docker build -t myapp:{version_str} .",
                f"docker tag myapp:{version_str} myapp:latest"
            ]
        }
        
        return commands
    
    def generate_file_updates(self, new_version: Version) -> Dict[str, str]:
        """Generate file update snippets for common package files."""
        version_str = new_version.to_string()
        
        updates = {}
        
        # package.json
        updates['package.json'] = json.dumps({
            "name": "your-package",
            "version": version_str,
            "description": "Your package description",
            "main": "index.js"
        }, indent=2)
        
        # pyproject.toml
        updates['pyproject.toml'] = f'''[build-system]
requires = ["setuptools>=61.0", "wheel"]
build-backend = "setuptools.build_meta"

[project]
name = "your-package"
version = "{version_str}"
description = "Your package description"
authors = [
    {{name = "Your Name", email = "your.email@example.com"}},
]
'''
        
        # setup.py  
        updates['setup.py'] = f'''from setuptools import setup, find_packages

setup(
    name="your-package",
    version="{version_str}",
    description="Your package description",
    packages=find_packages(),
    python_requires=">=3.8",
)
'''
        
        # Cargo.toml
        updates['Cargo.toml'] = f'''[package]
name = "your-package"
version = "{version_str}"
edition = "2021"
description = "Your package description"
'''
        
        # __init__.py
        updates['__init__.py'] = f'''"""Your package."""

__version__ = "{version_str}"
__author__ = "Your Name"
__email__ = "your.email@example.com"
'''
        
        return updates
    
    def analyze_commits(self) -> Dict:
        """Provide detailed analysis of commits for version bumping."""
        if not self.commits:
            return {
                'total_commits': 0,
                'by_type': {},
                'breaking_changes': [],
                'features': [],
                'fixes': [],
                'ignored': []
            }
        
        analysis = {
            'total_commits': len(self.commits),
            'by_type': {},
            'breaking_changes': [],
            'features': [],
            'fixes': [],
            'ignored': []
        }
        
        type_counts = {}
        for commit in self.commits:
            type_counts[commit.type] = type_counts.get(commit.type, 0) + 1
            
            if commit.is_breaking:
                analysis['breaking_changes'].append({
                    'type': commit.type,
                    'scope': commit.scope,
                    'description': commit.description,
                    'breaking_description': commit.breaking_description,
                    'hash': commit.hash
                })
            elif commit.type in ['feat', 'add']:
                analysis['features'].append({
                    'scope': commit.scope,
                    'description': commit.description,
                    'hash': commit.hash
                })
            elif commit.type in ['fix', 'security', 'perf', 'bugfix']:
                analysis['fixes'].append({
                    'scope': commit.scope, 
                    'description': commit.description,
                    'hash': commit.hash
                })
            elif commit.type in self.ignore_types:
                analysis['ignored'].append({
                    'type': commit.type,
                    'scope': commit.scope,
                    'description': commit.description,
                    'hash': commit.hash
                })
        
        analysis['by_type'] = type_counts
        return analysis


def main():
    """Main CLI entry point."""
    parser = argparse.ArgumentParser(description="Determine version bump based on conventional commits")
    parser.add_argument('--current-version', '-c', required=True,
                       help='Current version (e.g., 1.2.3, v1.2.3)')
    parser.add_argument('--input', '-i', type=str,
                       help='Input file with commits (default: stdin)')
    parser.add_argument('--input-format', choices=['git-log', 'json'], 
                       default='git-log', help='Input format')
    parser.add_argument('--prerelease', '-p', 
                       choices=['alpha', 'beta', 'rc'],
                       help='Generate pre-release version')
    parser.add_argument('--output-format', '-f', 
                       choices=['text', 'json', 'commands'], 
                       default='text', help='Output format')
    parser.add_argument('--output', '-o', type=str,
                       help='Output file (default: stdout)')
    parser.add_argument('--include-commands', action='store_true',
                       help='Include bump commands in output')
    parser.add_argument('--include-files', action='store_true',
                       help='Include file update snippets')
    parser.add_argument('--custom-rules', type=str,
                       help='JSON string with custom type->bump rules')
    parser.add_argument('--ignore-types', type=str,
                       help='Comma-separated list of types to ignore')
    parser.add_argument('--analysis', '-a', action='store_true',
                       help='Include detailed commit analysis')
    
    args = parser.parse_args()
    
    # Read input
    if args.input:
        with open(args.input, 'r', encoding='utf-8') as f:
            input_data = f.read()
    else:
        input_data = sys.stdin.read()
    
    if not input_data.strip():
        print("No input data provided", file=sys.stderr)
        sys.exit(1)
    
    # Initialize version bumper
    bumper = VersionBumper()
    
    try:
        bumper.set_current_version(args.current_version)
    except ValueError as e:
        print(f"Invalid current version: {e}", file=sys.stderr)
        sys.exit(1)
    
    # Apply custom rules
    if args.custom_rules:
        try:
            custom_rules = json.loads(args.custom_rules)
            for commit_type, bump_type_str in custom_rules.items():
                bump_type = BumpType(bump_type_str.lower())
                bumper.add_custom_rule(commit_type, bump_type)
        except Exception as e:
            print(f"Invalid custom rules: {e}", file=sys.stderr)
            sys.exit(1)
    
    # Set ignore types
    if args.ignore_types:
        bumper.ignore_types = [t.strip() for t in args.ignore_types.split(',')]
    
    # Parse commits
    try:
        if args.input_format == 'json':
            bumper.parse_commits_from_json(input_data)
        else:
            bumper.parse_commits_from_git_log(input_data)
    except Exception as e:
        print(f"Error parsing commits: {e}", file=sys.stderr)
        sys.exit(1)
    
    # Determine pre-release type
    prerelease_type = None
    if args.prerelease:
        prerelease_type = PreReleaseType(args.prerelease)
    
    # Generate recommendation
    try:
        recommended_version = bumper.recommend_version(prerelease_type)
        bump_type = bumper.determine_bump_type()
    except Exception as e:
        print(f"Error determining version: {e}", file=sys.stderr)
        sys.exit(1)
    
    # Generate output
    output_data = {}
    
    if args.output_format == 'json':
        output_data = {
            'current_version': args.current_version,
            'recommended_version': recommended_version.to_string(),
            'recommended_version_with_v': recommended_version.to_string(include_v_prefix=True),
            'bump_type': bump_type.value,
            'prerelease': args.prerelease
        }
        
        if args.analysis:
            output_data['analysis'] = bumper.analyze_commits()
        
        if args.include_commands:
            output_data['commands'] = bumper.generate_bump_commands(recommended_version)
        
        if args.include_files:
            output_data['file_updates'] = bumper.generate_file_updates(recommended_version)
        
        output_text = json.dumps(output_data, indent=2)
    
    elif args.output_format == 'commands':
        commands = bumper.generate_bump_commands(recommended_version)
        output_lines = [
            f"# Version Bump Commands",
            f"# Current: {args.current_version}",
            f"# New: {recommended_version.to_string()}",
            f"# Bump Type: {bump_type.value}",
            ""
        ]
        
        for category, cmd_list in commands.items():
            output_lines.append(f"## {category.upper()}")
            for cmd in cmd_list:
                output_lines.append(cmd)
            output_lines.append("")
        
        output_text = '\n'.join(output_lines)
    
    else:  # text format
        output_lines = [
            f"Current Version: {args.current_version}",
            f"Recommended Version: {recommended_version.to_string()}",
            f"With v prefix: {recommended_version.to_string(include_v_prefix=True)}",
            f"Bump Type: {bump_type.value}",
            ""
        ]
        
        if args.analysis:
            analysis = bumper.analyze_commits()
            output_lines.extend([
                "Commit Analysis:",
                f"- Total commits: {analysis['total_commits']}",
                f"- Breaking changes: {len(analysis['breaking_changes'])}",
                f"- New features: {len(analysis['features'])}",
                f"- Bug fixes: {len(analysis['fixes'])}",
                f"- Ignored commits: {len(analysis['ignored'])}",
                ""
            ])
            
            if analysis['breaking_changes']:
                output_lines.append("Breaking Changes:")
                for change in analysis['breaking_changes']:
                    scope = f"({change['scope']})" if change['scope'] else ""
                    output_lines.append(f"  - {change['type']}{scope}: {change['description']}")
                output_lines.append("")
        
        if args.include_commands:
            commands = bumper.generate_bump_commands(recommended_version)
            output_lines.append("Bump Commands:")
            for category, cmd_list in commands.items():
                output_lines.append(f"  {category}:")
                for cmd in cmd_list:
                    if not cmd.startswith('#'):
                        output_lines.append(f"    {cmd}")
            output_lines.append("")
        
        output_text = '\n'.join(output_lines)
    
    # Write output
    if args.output:
        with open(args.output, 'w', encoding='utf-8') as f:
            f.write(output_text)
    else:
        print(output_text)


if __name__ == '__main__':
    main()