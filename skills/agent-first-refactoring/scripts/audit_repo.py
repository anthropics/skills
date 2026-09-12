#!/usr/bin/env python3
"""Audit a repository for agent-first readiness.

Checks for the presence and quality of AGENTS.md, test suite characteristics,
component interface quality, tool accessibility, and CI configuration.

Usage:
    python audit_repo.py <path-to-repo> [--format text|json]
    python audit_repo.py --help
"""

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path


@dataclass
class CheckResult:
    name: str
    status: str  # "pass", "warn", "fail"
    message: str
    suggestions: list[str] = field(default_factory=list)


@dataclass
class AuditReport:
    repo_path: str
    checks: list[CheckResult] = field(default_factory=list)

    @property
    def score(self) -> int:
        if not self.checks:
            return 0
        points = {"pass": 2, "warn": 1, "fail": 0}
        total = sum(points.get(c.status, 0) for c in self.checks)
        max_score = len(self.checks) * 2
        return round((total / max_score) * 100)

    def to_dict(self) -> dict:
        return {
            "repo_path": self.repo_path,
            "score": self.score,
            "summary": self.summary_line,
            "checks": [
                {
                    "name": c.name,
                    "status": c.status,
                    "message": c.message,
                    "suggestions": c.suggestions,
                }
                for c in self.checks
            ],
        }

    @property
    def summary_line(self) -> str:
        counts = {"pass": 0, "warn": 0, "fail": 0}
        for c in self.checks:
            counts[c.status] = counts.get(c.status, 0) + 1
        return (
            f"Score: {self.score}/100 — "
            f"{counts['pass']} passed, "
            f"{counts['warn']} warnings, "
            f"{counts['fail']} failed"
        )

    def to_text(self) -> str:
        lines = []
        lines.append("=" * 60)
        lines.append("  Agent-First Repository Audit Report")
        lines.append("=" * 60)
        lines.append(f"  Repository: {self.repo_path}")
        lines.append(f"  {self.summary_line}")
        lines.append("=" * 60)
        lines.append("")

        status_icons = {"pass": "[PASS]", "warn": "[WARN]", "fail": "[FAIL]"}

        for check in self.checks:
            icon = status_icons.get(check.status, "[????]")
            lines.append(f"{icon} {check.name}")
            lines.append(f"       {check.message}")
            for suggestion in check.suggestions:
                lines.append(f"       -> {suggestion}")
            lines.append("")

        # Priority actions
        failures = [c for c in self.checks if c.status == "fail"]
        warnings = [c for c in self.checks if c.status == "warn"]

        if failures or warnings:
            lines.append("-" * 60)
            lines.append("  Priority Actions")
            lines.append("-" * 60)
            for i, check in enumerate(failures + warnings, 1):
                for suggestion in check.suggestions:
                    lines.append(f"  {i}. {suggestion}")
            lines.append("")

        return "\n".join(lines)


def check_agents_md(repo: Path) -> CheckResult:
    """Check for presence and quality of AGENTS.md or CLAUDE.md."""
    candidates = ["AGENTS.md", "CLAUDE.md", "agents.md", "claude.md"]
    found = None
    for name in candidates:
        path = repo / name
        if path.exists():
            found = path
            break

    if not found:
        return CheckResult(
            name="AGENTS.md presence",
            status="fail",
            message="No AGENTS.md or CLAUDE.md found at repository root.",
            suggestions=[
                "Create an AGENTS.md at the repo root with build/test commands, "
                "project structure, conventions, and common pitfalls."
            ],
        )

    content = found.read_text(errors="replace")
    lines = content.strip().split("\n")
    issues = []
    suggestions = []

    if len(lines) < 10:
        issues.append("File is very short (< 10 lines)")
        suggestions.append("Expand AGENTS.md with test commands, project structure, and pitfalls.")

    # Check for essential sections
    content_lower = content.lower()
    essential_keywords = {
        "test": "test commands",
        "build": "build/run commands",
        "structure": "project structure",
    }
    for keyword, desc in essential_keywords.items():
        if keyword not in content_lower:
            issues.append(f"Missing section about {desc}")
            suggestions.append(f"Add a section describing {desc} to {found.name}.")

    if not issues:
        return CheckResult(
            name="AGENTS.md presence",
            status="pass",
            message=f"Found {found.name} ({len(lines)} lines) with essential sections.",
        )
    else:
        return CheckResult(
            name="AGENTS.md quality",
            status="warn",
            message=f"Found {found.name} but it may be incomplete: {'; '.join(issues)}.",
            suggestions=suggestions,
        )


def check_test_presence(repo: Path) -> CheckResult:
    """Check for test files."""
    test_patterns = [
        "test_*.py", "*_test.py", "*.test.ts", "*.test.js",
        "*.spec.ts", "*.spec.js", "*_test.go", "*_test.rs",
    ]
    test_dirs = ["tests", "test", "spec", "__tests__", "src"]
    test_files = []

    for tdir in test_dirs:
        dirpath = repo / tdir
        if dirpath.is_dir():
            for pattern in test_patterns:
                test_files.extend(dirpath.rglob(pattern))

    # Also check root-level test files
    for pattern in test_patterns:
        test_files.extend(repo.glob(pattern))

    test_files = list(set(test_files))

    if not test_files:
        return CheckResult(
            name="Test suite presence",
            status="fail",
            message="No test files found.",
            suggestions=[
                "Add tests. Agents rely on tests as their primary feedback loop.",
                "Start with unit tests for core business logic.",
            ],
        )

    return CheckResult(
        name="Test suite presence",
        status="pass",
        message=f"Found {len(test_files)} test file(s).",
    )


def check_test_config(repo: Path) -> CheckResult:
    """Check for test configuration that supports selective execution."""
    config_files = {
        "pytest.ini": "pytest",
        "pyproject.toml": "Python project",
        "setup.cfg": "Python project",
        "jest.config.js": "Jest",
        "jest.config.ts": "Jest",
        "vitest.config.ts": "Vitest",
        "vitest.config.js": "Vitest",
        ".mocharc.yml": "Mocha",
        "go.mod": "Go module",
        "Cargo.toml": "Rust/Cargo",
    }

    found = []
    for filename, framework in config_files.items():
        if (repo / filename).exists():
            found.append((filename, framework))

    if not found:
        return CheckResult(
            name="Test configuration",
            status="warn",
            message="No standard test configuration files found.",
            suggestions=[
                "Add test configuration (pytest.ini, jest.config.js, etc.) "
                "to support selective test execution."
            ],
        )

    frameworks = ", ".join(f"{fw} ({fn})" for fn, fw in found)
    return CheckResult(
        name="Test configuration",
        status="pass",
        message=f"Test configuration found: {frameworks}.",
    )


def check_type_checking(repo: Path) -> CheckResult:
    """Check for type checking configuration."""
    type_configs = {
        "tsconfig.json": "TypeScript",
        "mypy.ini": "mypy",
        ".mypy.ini": "mypy",
        "pyrightconfig.json": "Pyright",
    }

    # Also check pyproject.toml for mypy/pyright config
    pyproject = repo / "pyproject.toml"
    found = []

    for filename, tool in type_configs.items():
        if (repo / filename).exists():
            found.append(tool)

    if pyproject.exists():
        content = pyproject.read_text(errors="replace")
        if "[tool.mypy]" in content:
            found.append("mypy (pyproject.toml)")
        if "[tool.pyright]" in content:
            found.append("Pyright (pyproject.toml)")

    if not found:
        return CheckResult(
            name="Type checking",
            status="warn",
            message="No type checking configuration found.",
            suggestions=[
                "Add type checking (TypeScript, mypy, Pyright) to catch errors "
                "at module boundaries. Agents rely on types to understand interfaces."
            ],
        )

    return CheckResult(
        name="Type checking",
        status="pass",
        message=f"Type checking configured: {', '.join(found)}.",
    )


def check_linting(repo: Path) -> CheckResult:
    """Check for linting/formatting configuration."""
    lint_configs = {
        ".eslintrc": "ESLint", ".eslintrc.js": "ESLint", ".eslintrc.json": "ESLint",
        "eslint.config.js": "ESLint", "eslint.config.mjs": "ESLint",
        ".prettierrc": "Prettier", ".prettierrc.json": "Prettier",
        "ruff.toml": "Ruff",
        ".flake8": "Flake8",
        ".golangci.yml": "golangci-lint", ".golangci.yaml": "golangci-lint",
        "rustfmt.toml": "rustfmt", ".rustfmt.toml": "rustfmt",
        "biome.json": "Biome",
    }

    found = []
    for filename, tool in lint_configs.items():
        if (repo / filename).exists():
            found.append(tool)

    # Check pyproject.toml for ruff/black
    pyproject = repo / "pyproject.toml"
    if pyproject.exists():
        content = pyproject.read_text(errors="replace")
        if "[tool.ruff]" in content:
            found.append("Ruff (pyproject.toml)")
        if "[tool.black]" in content:
            found.append("Black (pyproject.toml)")

    found = list(set(found))

    if not found:
        return CheckResult(
            name="Linting and formatting",
            status="warn",
            message="No linting or formatting configuration found.",
            suggestions=[
                "Add a linter and formatter (ESLint+Prettier, Ruff, golangci-lint) "
                "so agents can auto-fix style issues."
            ],
        )

    return CheckResult(
        name="Linting and formatting",
        status="pass",
        message=f"Linting/formatting configured: {', '.join(found)}.",
    )


def check_ci_config(repo: Path) -> CheckResult:
    """Check for CI/CD configuration."""
    ci_paths = [
        ".github/workflows",
        ".gitlab-ci.yml",
        ".circleci",
        "Jenkinsfile",
        ".buildkite",
        "azure-pipelines.yml",
        ".travis.yml",
    ]

    found = []
    for ci_path in ci_paths:
        full_path = repo / ci_path
        if full_path.exists():
            found.append(ci_path)

    if not found:
        return CheckResult(
            name="CI/CD configuration",
            status="warn",
            message="No CI/CD configuration found.",
            suggestions=[
                "Add CI (GitHub Actions, GitLab CI, etc.) to run linting, type "
                "checking, and tests automatically on PRs."
            ],
        )

    return CheckResult(
        name="CI/CD configuration",
        status="pass",
        message=f"CI/CD found: {', '.join(found)}.",
    )


def check_module_boundaries(repo: Path) -> CheckResult:
    """Check for explicit module boundary patterns."""
    # Look for barrel/index files that indicate explicit exports
    barrel_patterns = ["**/index.ts", "**/index.js", "**/__init__.py"]
    barrel_files = []
    for pattern in barrel_patterns:
        barrel_files.extend(repo.glob(pattern))

    # Filter out node_modules and other irrelevant dirs
    barrel_files = [
        f for f in barrel_files
        if "node_modules" not in str(f)
        and ".venv" not in str(f)
        and "venv" not in str(f)
        and "__pycache__" not in str(f)
    ]

    if len(barrel_files) >= 3:
        return CheckResult(
            name="Module boundaries",
            status="pass",
            message=f"Found {len(barrel_files)} module boundary files (index/init).",
        )
    elif barrel_files:
        return CheckResult(
            name="Module boundaries",
            status="warn",
            message=f"Found only {len(barrel_files)} module boundary file(s).",
            suggestions=[
                "Add __init__.py or index.ts files to define explicit public APIs "
                "for each major module."
            ],
        )
    else:
        return CheckResult(
            name="Module boundaries",
            status="warn",
            message="No explicit module boundary files found.",
            suggestions=[
                "Define explicit module boundaries with __init__.py (Python) "
                "or index.ts (TypeScript) files that export public APIs."
            ],
        )


def check_makefile_or_scripts(repo: Path) -> CheckResult:
    """Check for development scripts/Makefile."""
    script_files = ["Makefile", "justfile", "Taskfile.yml", "package.json"]
    script_dirs = ["scripts", "bin", "tools"]

    found_files = [f for f in script_files if (repo / f).exists()]
    found_dirs = [d for d in script_dirs if (repo / d).is_dir()]

    if not found_files and not found_dirs:
        return CheckResult(
            name="Development scripts",
            status="warn",
            message="No Makefile, task runner, or scripts directory found.",
            suggestions=[
                "Add a Makefile or scripts/ directory with common commands "
                "(build, test, lint, deploy) so agents can discover and run them."
            ],
        )

    items = found_files + found_dirs
    return CheckResult(
        name="Development scripts",
        status="pass",
        message=f"Development scripts found: {', '.join(items)}.",
    )


def check_env_example(repo: Path) -> CheckResult:
    """Check for environment variable documentation."""
    env_files = [".env.example", ".env.template", ".env.sample", "env.example"]
    found = [f for f in env_files if (repo / f).exists()]

    if not found:
        # Check if there's a .env file without an example
        if (repo / ".env").exists():
            return CheckResult(
                name="Environment documentation",
                status="warn",
                message="Found .env but no .env.example.",
                suggestions=[
                    "Create a .env.example with all required environment variables "
                    "(without secret values) so agents know what configuration is needed."
                ],
            )
        return CheckResult(
            name="Environment documentation",
            status="pass",
            message="No .env files detected (may not be needed).",
        )

    return CheckResult(
        name="Environment documentation",
        status="pass",
        message=f"Environment documented: {', '.join(found)}.",
    )


def run_audit(repo_path: str) -> AuditReport:
    """Run all audit checks on a repository."""
    repo = Path(repo_path).resolve()
    if not repo.is_dir():
        print(f"Error: {repo_path} is not a directory", file=sys.stderr)
        sys.exit(1)

    report = AuditReport(repo_path=str(repo))

    checks = [
        check_agents_md,
        check_test_presence,
        check_test_config,
        check_type_checking,
        check_linting,
        check_ci_config,
        check_module_boundaries,
        check_makefile_or_scripts,
        check_env_example,
    ]

    for check_fn in checks:
        try:
            result = check_fn(repo)
            report.checks.append(result)
        except Exception as e:
            report.checks.append(
                CheckResult(
                    name=check_fn.__doc__ or check_fn.__name__,
                    status="warn",
                    message=f"Check failed with error: {e}",
                )
            )

    return report


def main():
    parser = argparse.ArgumentParser(
        description="Audit a repository for agent-first readiness."
    )
    parser.add_argument("repo", help="Path to the repository to audit")
    parser.add_argument(
        "--format",
        choices=["text", "json"],
        default="text",
        help="Output format (default: text)",
    )
    args = parser.parse_args()

    report = run_audit(args.repo)

    if args.format == "json":
        print(json.dumps(report.to_dict(), indent=2))
    else:
        print(report.to_text())

    # Exit with non-zero if any failures
    if any(c.status == "fail" for c in report.checks):
        sys.exit(1)


if __name__ == "__main__":
    main()
