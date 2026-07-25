#!/usr/bin/env python3
"""
Code Quality Analyzer

Analyzes fullstack codebases for quality issues including:
- Code complexity metrics (cyclomatic complexity, cognitive complexity)
- Security vulnerabilities (hardcoded secrets, injection patterns)
- Dependency health (outdated packages, known vulnerabilities)
- Test coverage estimation
- Documentation quality

Usage:
    python code_quality_analyzer.py /path/to/project
    python code_quality_analyzer.py . --json
    python code_quality_analyzer.py /path/to/project --output report.json
"""

import argparse
import json
import os
import re
import sys
from collections import defaultdict
from pathlib import Path
from typing import Dict, List, Optional, Tuple


# File extensions to analyze
FRONTEND_EXTENSIONS = {".ts", ".tsx", ".js", ".jsx", ".vue", ".svelte"}
BACKEND_EXTENSIONS = {".py", ".go", ".java", ".rb", ".php", ".cs"}
CONFIG_EXTENSIONS = {".json", ".yaml", ".yml", ".toml", ".env"}
ALL_CODE_EXTENSIONS = FRONTEND_EXTENSIONS | BACKEND_EXTENSIONS

# Skip patterns
SKIP_DIRS = {"node_modules", "vendor", ".git", "__pycache__", "dist", "build",
             ".next", ".venv", "venv", "env", "coverage", ".pytest_cache"}

# Security patterns to detect
SECURITY_PATTERNS = {
    "hardcoded_secret": {
        "pattern": r"(?:password|secret|api_key|apikey|token|auth)[\s]*[=:][\s]*['\"][^'\"]{8,}['\"]",
        "severity": "critical",
        "message": "Potential hardcoded secret detected"
    },
    "sql_injection": {
        "pattern": r"(?:execute|query|raw)\s*\(\s*[f'\"].*\{.*\}|%s|%d|\$\d",
        "severity": "high",
        "message": "Potential SQL injection vulnerability"
    },
    "xss_vulnerable": {
        "pattern": r"innerHTML\s*=|v-html",
        "severity": "medium",
        "message": "Potential XSS vulnerability - unescaped HTML rendering"
    },
    "unsafe_react_html": {
        "pattern": r"__html",
        "severity": "medium",
        "message": "React unsafe HTML pattern detected - ensure content is sanitized"
    },
    "insecure_protocol": {
        "pattern": r"http://(?!localhost|127\.0\.0\.1)",
        "severity": "medium",
        "message": "Insecure HTTP protocol used"
    },
    "debug_code": {
        "pattern": r"console\.log|print\(|debugger|DEBUG\s*=\s*True",
        "severity": "low",
        "message": "Debug code should be removed in production"
    },
    "todo_fixme": {
        "pattern": r"(?:TODO|FIXME|HACK|XXX):",
        "severity": "info",
        "message": "Unresolved TODO/FIXME comment"
    }
}

# Code smell patterns
CODE_SMELL_PATTERNS = {
    "long_function": {
        "description": "Function exceeds recommended length",
        "threshold": 50
    },
    "deep_nesting": {
        "description": "Excessive nesting depth",
        "threshold": 4
    },
    "large_file": {
        "description": "File exceeds recommended size",
        "threshold": 500
    },
    "magic_number": {
        "pattern": r"(?<![a-zA-Z_])\b(?:[2-9]\d{2,}|\d{4,})\b(?![a-zA-Z_])",
        "description": "Magic number should be named constant"
    }
}

# Dependency vulnerability patterns (simplified - in production use a CVE database)
KNOWN_VULNERABLE_DEPS = {
    "lodash": {"vulnerable_below": "4.17.21", "cve": "CVE-2021-23337"},
    "axios": {"vulnerable_below": "0.21.2", "cve": "CVE-2021-3749"},
    "minimist": {"vulnerable_below": "1.2.6", "cve": "CVE-2021-44906"},
    "jsonwebtoken": {"vulnerable_below": "9.0.0", "cve": "CVE-2022-23529"},
}


def should_skip(path: Path) -> bool:
    """Check if path should be skipped."""
    return any(skip in path.parts for skip in SKIP_DIRS)


def count_lines(filepath: Path) -> Tuple[int, int, int]:
    """Count total lines, code lines, and comment lines."""
    try:
        with open(filepath, "r", encoding="utf-8", errors="ignore") as f:
            lines = f.readlines()
    except Exception:
        return 0, 0, 0

    total = len(lines)
    code = 0
    comments = 0
    in_block_comment = False

    for line in lines:
        stripped = line.strip()
        if not stripped:
            continue

        # Block comments
        if "/*" in stripped:
            in_block_comment = True
        if in_block_comment:
            comments += 1
            if "*/" in stripped:
                in_block_comment = False
            continue

        # Line comments
        if stripped.startswith(("//", "#", "--", "'")):
            comments += 1
        else:
            code += 1

    return total, code, comments


def calculate_complexity(content: str, language: str) -> Dict:
    """Calculate cyclomatic complexity estimate."""
    # Count decision points
    decision_patterns = [
        r"\bif\b", r"\belse\b", r"\belif\b", r"\bfor\b", r"\bwhile\b",
        r"\bcase\b", r"\bcatch\b", r"\b\?\b", r"\b&&\b", r"\b\|\|\b",
        r"\band\b", r"\bor\b"
    ]

    complexity = 1  # Base complexity
    for pattern in decision_patterns:
        complexity += len(re.findall(pattern, content, re.IGNORECASE))

    # Count nesting depth
    max_depth = 0
    current_depth = 0
    for char in content:
        if char == "{":
            current_depth += 1
            max_depth = max(max_depth, current_depth)
        elif char == "}":
            current_depth = max(0, current_depth - 1)

    return {
        "cyclomatic": complexity,
        "max_nesting": max_depth,
        "rating": "low" if complexity < 10 else "medium" if complexity < 20 else "high"
    }


def analyze_security(filepath: Path, content: str) -> List[Dict]:
    """Scan for security issues."""
    issues = []
    lines = content.split("\n")

    for pattern_name, pattern_info in SECURITY_PATTERNS.items():
        regex = re.compile(pattern_info["pattern"], re.IGNORECASE)
        for line_num, line in enumerate(lines, 1):
            if regex.search(line):
                issues.append({
                    "file": str(filepath),
                    "line": line_num,
                    "type": pattern_name,
                    "severity": pattern_info["severity"],
                    "message": pattern_info["message"]
                })

    return issues


def analyze_dependencies(project_path: Path) -> Dict:
    """Analyze project dependencies for issues."""
    findings = {
        "package_managers": [],
        "total_deps": 0,
        "outdated": [],
        "vulnerable": [],
        "recommendations": []
    }

    # Check package.json
    package_json = project_path / "package.json"
    if package_json.exists():
        findings["package_managers"].append("npm")
        try:
            with open(package_json) as f:
                pkg = json.load(f)
            deps = {**pkg.get("dependencies", {}), **pkg.get("devDependencies", {})}
            findings["total_deps"] += len(deps)

            for dep, version in deps.items():
                # Check against known vulnerabilities
                if dep in KNOWN_VULNERABLE_DEPS:
                    vuln = KNOWN_VULNERABLE_DEPS[dep]
                    # Simplified version check
                    clean_version = re.sub(r"[^\d.]", "", version)
                    if clean_version and clean_version < vuln["vulnerable_below"]:
                        findings["vulnerable"].append({
                            "package": dep,
                            "current": version,
                            "fix_version": vuln["vulnerable_below"],
                            "cve": vuln["cve"]
                        })
        except Exception:
            pass

    # Check requirements.txt
    requirements = project_path / "requirements.txt"
    if requirements.exists():
        findings["package_managers"].append("pip")
        try:
            with open(requirements) as f:
                lines = [l.strip() for l in f if l.strip() and not l.startswith("#")]
            findings["total_deps"] += len(lines)
        except Exception:
            pass

    # Check go.mod
    go_mod = project_path / "go.mod"
    if go_mod.exists():
        findings["package_managers"].append("go")

    return findings


def analyze_test_coverage(project_path: Path) -> Dict:
    """Estimate test coverage based on file analysis."""
    test_files = []
    source_files = []

    for filepath in project_path.rglob("*"):
        if should_skip(filepath) or not filepath.is_file():
            continue

        if filepath.suffix in ALL_CODE_EXTENSIONS:
            name = filepath.stem.lower()
            if "test" in name or "spec" in name or "_test" in name:
                test_files.append(filepath)
            elif not name.startswith("_"):
                source_files.append(filepath)

    source_count = len(source_files)
    test_count = len(test_files)

    # Estimate coverage ratio
    if source_count == 0:
        ratio = 0
    else:
        ratio = min(100, int((test_count / source_count) * 100))

    return {
        "source_files": source_count,
        "test_files": test_count,
        "estimated_coverage": ratio,
        "rating": "good" if ratio >= 70 else "adequate" if ratio >= 40 else "poor",
        "recommendation": None if ratio >= 70 else f"Consider adding more tests ({70 - ratio}% gap to target)"
    }


def analyze_documentation(project_path: Path) -> Dict:
    """Analyze documentation quality."""
    docs = {
        "has_readme": False,
        "has_contributing": False,
        "has_license": False,
        "has_changelog": False,
        "api_docs": [],
        "score": 0
    }

    readme_patterns = ["README.md", "README.rst", "README.txt", "readme.md"]
    for pattern in readme_patterns:
        if (project_path / pattern).exists():
            docs["has_readme"] = True
            docs["score"] += 30
            break

    if (project_path / "CONTRIBUTING.md").exists():
        docs["has_contributing"] = True
        docs["score"] += 15

    license_patterns = ["LICENSE", "LICENSE.md", "LICENSE.txt"]
    for pattern in license_patterns:
        if (project_path / pattern).exists():
            docs["has_license"] = True
            docs["score"] += 15
            break

    changelog_patterns = ["CHANGELOG.md", "HISTORY.md", "CHANGES.md"]
    for pattern in changelog_patterns:
        if (project_path / pattern).exists():
            docs["has_changelog"] = True
            docs["score"] += 10
            break

    # Check for API docs
    api_doc_dirs = ["docs", "documentation", "api-docs"]
    for doc_dir in api_doc_dirs:
        doc_path = project_path / doc_dir
        if doc_path.is_dir():
            docs["api_docs"].append(str(doc_path))
            docs["score"] += 30
            break

    return docs


def analyze_project(project_path: Path) -> Dict:
    """Perform full project analysis."""
    results = {
        "summary": {
            "files_analyzed": 0,
            "total_lines": 0,
            "code_lines": 0,
            "comment_lines": 0
        },
        "languages": defaultdict(lambda: {"files": 0, "lines": 0}),
        "security": {
            "critical": [],
            "high": [],
            "medium": [],
            "low": [],
            "info": []
        },
        "complexity": {
            "high_complexity_files": [],
            "average_complexity": 0
        },
        "code_smells": [],
        "dependencies": {},
        "tests": {},
        "documentation": {},
        "overall_score": 100
    }

    complexity_scores = []
    security_issues = []

    # Analyze source files
    for filepath in project_path.rglob("*"):
        if should_skip(filepath) or not filepath.is_file():
            continue

        if filepath.suffix not in ALL_CODE_EXTENSIONS:
            continue

        results["summary"]["files_analyzed"] += 1

        # Count lines
        total, code, comments = count_lines(filepath)
        results["summary"]["total_lines"] += total
        results["summary"]["code_lines"] += code
        results["summary"]["comment_lines"] += comments

        # Track by language
        lang = "typescript" if filepath.suffix in {".ts", ".tsx"} else \
               "javascript" if filepath.suffix in {".js", ".jsx"} else \
               "python" if filepath.suffix == ".py" else \
               "go" if filepath.suffix == ".go" else "other"
        results["languages"][lang]["files"] += 1
        results["languages"][lang]["lines"] += code

        # Read file content
        try:
            with open(filepath, "r", encoding="utf-8", errors="ignore") as f:
                content = f.read()
        except Exception:
            continue

        # Complexity analysis
        complexity = calculate_complexity(content, lang)
        complexity_scores.append(complexity["cyclomatic"])
        if complexity["rating"] == "high":
            results["complexity"]["high_complexity_files"].append({
                "file": str(filepath.relative_to(project_path)),
                "complexity": complexity["cyclomatic"],
                "nesting": complexity["max_nesting"]
            })

        # Security analysis
        issues = analyze_security(filepath.relative_to(project_path), content)
        security_issues.extend(issues)

        # Code smell: large file
        if total > CODE_SMELL_PATTERNS["large_file"]["threshold"]:
            results["code_smells"].append({
                "file": str(filepath.relative_to(project_path)),
                "type": "large_file",
                "details": f"{total} lines (threshold: {CODE_SMELL_PATTERNS['large_file']['threshold']})"
            })

    # Categorize security issues
    for issue in security_issues:
        severity = issue["severity"]
        results["security"][severity].append(issue)

    # Calculate average complexity
    if complexity_scores:
        results["complexity"]["average_complexity"] = round(
            sum(complexity_scores) / len(complexity_scores), 1
        )

    # Dependency analysis
    results["dependencies"] = analyze_dependencies(project_path)

    # Test coverage analysis
    results["tests"] = analyze_test_coverage(project_path)

    # Documentation analysis
    results["documentation"] = analyze_documentation(project_path)

    # Calculate overall score
    score = 100

    # Deduct for security issues
    score -= len(results["security"]["critical"]) * 15
    score -= len(results["security"]["high"]) * 10
    score -= len(results["security"]["medium"]) * 5
    score -= len(results["security"]["low"]) * 2

    # Deduct for high complexity
    score -= len(results["complexity"]["high_complexity_files"]) * 3

    # Deduct for code smells
    score -= len(results["code_smells"]) * 2

    # Deduct for vulnerable dependencies
    score -= len(results["dependencies"].get("vulnerable", [])) * 10

    # Deduct for poor test coverage
    if results["tests"].get("estimated_coverage", 0) < 50:
        score -= 15
    elif results["tests"].get("estimated_coverage", 0) < 70:
        score -= 5

    # Deduct for missing documentation
    doc_score = results["documentation"].get("score", 0)
    if doc_score < 50:
        score -= 10
    elif doc_score < 75:
        score -= 5

    results["overall_score"] = max(0, min(100, score))
    results["grade"] = (
        "A" if score >= 90 else
        "B" if score >= 80 else
        "C" if score >= 70 else
        "D" if score >= 60 else "F"
    )

    # Generate recommendations
    results["recommendations"] = generate_recommendations(results)

    # Convert defaultdict to regular dict for JSON serialization
    results["languages"] = dict(results["languages"])

    return results


def generate_recommendations(analysis: Dict) -> List[Dict]:
    """Generate prioritized recommendations."""
    recs = []

    # Critical security issues
    for issue in analysis["security"]["critical"][:3]:
        recs.append({
            "priority": "P0",
            "category": "security",
            "issue": issue["message"],
            "file": issue["file"],
            "action": f"Remove or secure sensitive data at line {issue['line']}"
        })

    # Vulnerable dependencies
    for vuln in analysis["dependencies"].get("vulnerable", [])[:3]:
        recs.append({
            "priority": "P0",
            "category": "security",
            "issue": f"Vulnerable dependency: {vuln['package']} ({vuln['cve']})",
            "action": f"Update to version {vuln['fix_version']} or later"
        })

    # High security issues
    for issue in analysis["security"]["high"][:3]:
        recs.append({
            "priority": "P1",
            "category": "security",
            "issue": issue["message"],
            "file": issue["file"],
            "action": "Review and fix security vulnerability"
        })

    # Test coverage
    tests = analysis.get("tests", {})
    if tests.get("estimated_coverage", 0) < 50:
        recs.append({
            "priority": "P1",
            "category": "quality",
            "issue": f"Low test coverage: {tests.get('estimated_coverage', 0)}%",
            "action": "Add unit tests to improve coverage to at least 70%"
        })

    # High complexity files
    for cplx in analysis["complexity"]["high_complexity_files"][:2]:
        recs.append({
            "priority": "P2",
            "category": "maintainability",
            "issue": f"High complexity in {cplx['file']}",
            "action": "Refactor to reduce cyclomatic complexity"
        })

    # Documentation
    docs = analysis.get("documentation", {})
    if not docs.get("has_readme"):
        recs.append({
            "priority": "P2",
            "category": "documentation",
            "issue": "Missing README.md",
            "action": "Add README with project overview and setup instructions"
        })

    return recs[:10]


def print_report(analysis: Dict, verbose: bool = False) -> None:
    """Print human-readable report."""
    print("=" * 60)
    print("CODE QUALITY ANALYSIS REPORT")
    print("=" * 60)
    print()

    # Summary
    summary = analysis["summary"]
    print(f"Overall Score: {analysis['overall_score']}/100 (Grade: {analysis['grade']})")
    print(f"Files Analyzed: {summary['files_analyzed']}")
    print(f"Total Lines: {summary['total_lines']:,}")
    print(f"Code Lines: {summary['code_lines']:,}")
    print(f"Comment Lines: {summary['comment_lines']:,}")
    print()

    # Languages
    print("--- LANGUAGES ---")
    for lang, stats in analysis["languages"].items():
        print(f"  {lang}: {stats['files']} files, {stats['lines']:,} lines")
    print()

    # Security
    sec = analysis["security"]
    total_sec = sum(len(sec[s]) for s in ["critical", "high", "medium", "low"])
    print("--- SECURITY ---")
    print(f"  Critical: {len(sec['critical'])}")
    print(f"  High: {len(sec['high'])}")
    print(f"  Medium: {len(sec['medium'])}")
    print(f"  Low: {len(sec['low'])}")
    if total_sec > 0 and verbose:
        print("  Issues:")
        for severity in ["critical", "high", "medium"]:
            for issue in sec[severity][:3]:
                print(f"    [{severity.upper()}] {issue['file']}:{issue['line']} - {issue['message']}")
    print()

    # Complexity
    cplx = analysis["complexity"]
    print("--- COMPLEXITY ---")
    print(f"  Average Complexity: {cplx['average_complexity']}")
    print(f"  High Complexity Files: {len(cplx['high_complexity_files'])}")
    print()

    # Dependencies
    deps = analysis["dependencies"]
    print("--- DEPENDENCIES ---")
    print(f"  Package Managers: {', '.join(deps.get('package_managers', ['none']))}")
    print(f"  Total Dependencies: {deps.get('total_deps', 0)}")
    print(f"  Vulnerable: {len(deps.get('vulnerable', []))}")
    print()

    # Tests
    tests = analysis["tests"]
    print("--- TEST COVERAGE ---")
    print(f"  Source Files: {tests.get('source_files', 0)}")
    print(f"  Test Files: {tests.get('test_files', 0)}")
    print(f"  Estimated Coverage: {tests.get('estimated_coverage', 0)}% ({tests.get('rating', 'unknown')})")
    print()

    # Documentation
    docs = analysis["documentation"]
    print("--- DOCUMENTATION ---")
    print(f"  README: {'Yes' if docs.get('has_readme') else 'No'}")
    print(f"  LICENSE: {'Yes' if docs.get('has_license') else 'No'}")
    print(f"  CONTRIBUTING: {'Yes' if docs.get('has_contributing') else 'No'}")
    print(f"  CHANGELOG: {'Yes' if docs.get('has_changelog') else 'No'}")
    print(f"  Score: {docs.get('score', 0)}/100")
    print()

    # Recommendations
    if analysis["recommendations"]:
        print("--- RECOMMENDATIONS ---")
        for i, rec in enumerate(analysis["recommendations"][:10], 1):
            print(f"\n{i}. [{rec['priority']}] {rec['category'].upper()}")
            print(f"   Issue: {rec['issue']}")
            print(f"   Action: {rec['action']}")

    print()
    print("=" * 60)


def main():
    parser = argparse.ArgumentParser(
        description="Analyze fullstack codebase for quality issues",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  %(prog)s /path/to/project
  %(prog)s . --verbose
  %(prog)s /path/to/project --json --output report.json
        """
    )
    parser.add_argument(
        "project_path",
        nargs="?",
        default=".",
        help="Path to project directory (default: current directory)"
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output in JSON format"
    )
    parser.add_argument(
        "--output", "-o",
        help="Write output to file"
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Show detailed findings"
    )

    args = parser.parse_args()

    project_path = Path(args.project_path).resolve()
    if not project_path.exists():
        print(f"Error: Path does not exist: {project_path}", file=sys.stderr)
        sys.exit(1)

    analysis = analyze_project(project_path)

    if args.json:
        output = json.dumps(analysis, indent=2)
        if args.output:
            with open(args.output, "w") as f:
                f.write(output)
            print(f"Report written to {args.output}")
        else:
            print(output)
    else:
        print_report(analysis, args.verbose)
        if args.output:
            with open(args.output, "w") as f:
                json.dump(analysis, f, indent=2)
            print(f"\nDetailed JSON report written to {args.output}")


if __name__ == "__main__":
    main()
