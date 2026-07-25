#!/usr/bin/env python3
"""
Frontend Bundle Analyzer

Analyzes package.json and project structure for bundle optimization opportunities,
heavy dependencies, and best practice recommendations.

Usage:
    python bundle_analyzer.py <project_dir>
    python bundle_analyzer.py . --json
    python bundle_analyzer.py /path/to/project --verbose
"""

import argparse
import json
import os
import re
import sys
from pathlib import Path
from typing import Dict, List, Optional, Any, Tuple


# Known heavy packages and their lighter alternatives
HEAVY_PACKAGES = {
    "moment": {
        "size": "290KB",
        "alternative": "date-fns (12KB) or dayjs (2KB)",
        "reason": "Large locale files bundled by default"
    },
    "lodash": {
        "size": "71KB",
        "alternative": "lodash-es with tree-shaking or individual imports (lodash/get)",
        "reason": "Full library often imported when only few functions needed"
    },
    "jquery": {
        "size": "87KB",
        "alternative": "Native DOM APIs or React/Vue patterns",
        "reason": "Rarely needed in modern frameworks"
    },
    "axios": {
        "size": "14KB",
        "alternative": "Native fetch API (0KB) or ky (3KB)",
        "reason": "Fetch API covers most use cases"
    },
    "underscore": {
        "size": "17KB",
        "alternative": "Native ES6+ methods or lodash-es",
        "reason": "Most utilities now in standard JavaScript"
    },
    "chart.js": {
        "size": "180KB",
        "alternative": "recharts (bundled with React) or lightweight-charts",
        "reason": "Consider if you need all chart types"
    },
    "three": {
        "size": "600KB",
        "alternative": "None - use dynamic import for 3D features",
        "reason": "Very large, should be lazy-loaded"
    },
    "firebase": {
        "size": "400KB+",
        "alternative": "Import specific modules (firebase/auth, firebase/firestore)",
        "reason": "Modular imports significantly reduce size"
    },
    "material-ui": {
        "size": "Large",
        "alternative": "shadcn/ui (copy-paste components) or Tailwind",
        "reason": "Heavy runtime, consider headless alternatives"
    },
    "@mui/material": {
        "size": "Large",
        "alternative": "shadcn/ui or Radix UI + Tailwind",
        "reason": "Heavy runtime, consider headless alternatives"
    },
    "antd": {
        "size": "Large",
        "alternative": "shadcn/ui or Radix UI + Tailwind",
        "reason": "Heavy runtime, consider headless alternatives"
    }
}

# Recommended optimizations by package
PACKAGE_OPTIMIZATIONS = {
    "react-icons": "Import individual icons: import { FaHome } from 'react-icons/fa'",
    "date-fns": "Use tree-shaking: import { format } from 'date-fns'",
    "@heroicons/react": "Already tree-shakeable, good choice",
    "lucide-react": "Already tree-shakeable, add to optimizePackageImports in next.config.js",
    "framer-motion": "Use dynamic import for non-critical animations",
    "recharts": "Consider lazy loading for dashboard charts",
}

# Development dependencies that should not be in dependencies
DEV_ONLY_PACKAGES = [
    "typescript", "@types/", "eslint", "prettier", "jest", "vitest",
    "@testing-library", "cypress", "playwright", "storybook", "@storybook",
    "webpack", "vite", "rollup", "esbuild", "tailwindcss", "postcss",
    "autoprefixer", "sass", "less", "husky", "lint-staged"
]


def load_package_json(project_dir: Path) -> Optional[Dict]:
    """Load and parse package.json."""
    package_path = project_dir / "package.json"
    if not package_path.exists():
        return None

    try:
        with open(package_path) as f:
            return json.load(f)
    except json.JSONDecodeError:
        return None


def analyze_dependencies(package_json: Dict) -> Dict:
    """Analyze dependencies for issues."""
    deps = package_json.get("dependencies", {})
    dev_deps = package_json.get("devDependencies", {})

    issues = []
    warnings = []
    optimizations = []

    # Check for heavy packages
    for pkg, info in HEAVY_PACKAGES.items():
        if pkg in deps:
            issues.append({
                "package": pkg,
                "type": "heavy_dependency",
                "size": info["size"],
                "alternative": info["alternative"],
                "reason": info["reason"]
            })

    # Check for dev dependencies in production
    for pkg in deps.keys():
        for dev_pattern in DEV_ONLY_PACKAGES:
            if dev_pattern in pkg:
                warnings.append({
                    "package": pkg,
                    "type": "dev_in_production",
                    "message": f"{pkg} should be in devDependencies, not dependencies"
                })

    # Check for optimization opportunities
    for pkg in deps.keys():
        for opt_pkg, opt_tip in PACKAGE_OPTIMIZATIONS.items():
            if opt_pkg in pkg:
                optimizations.append({
                    "package": pkg,
                    "tip": opt_tip
                })

    # Check for outdated React patterns
    if "prop-types" in deps and ("typescript" in dev_deps or "@types/react" in dev_deps):
        warnings.append({
            "package": "prop-types",
            "type": "redundant",
            "message": "prop-types is redundant when using TypeScript"
        })

    # Check for multiple state management libraries
    state_libs = ["redux", "@reduxjs/toolkit", "mobx", "zustand", "jotai", "recoil", "valtio"]
    found_state_libs = [lib for lib in state_libs if lib in deps]
    if len(found_state_libs) > 1:
        warnings.append({
            "packages": found_state_libs,
            "type": "multiple_state_libs",
            "message": f"Multiple state management libraries found: {', '.join(found_state_libs)}"
        })

    return {
        "total_dependencies": len(deps),
        "total_dev_dependencies": len(dev_deps),
        "issues": issues,
        "warnings": warnings,
        "optimizations": optimizations
    }


def check_nextjs_config(project_dir: Path) -> Dict:
    """Check Next.js configuration for optimizations."""
    config_paths = [
        project_dir / "next.config.js",
        project_dir / "next.config.mjs",
        project_dir / "next.config.ts"
    ]

    for config_path in config_paths:
        if config_path.exists():
            try:
                content = config_path.read_text()
                suggestions = []

                # Check for image optimization
                if "images" not in content:
                    suggestions.append("Configure images.remotePatterns for optimized image loading")

                # Check for package optimization
                if "optimizePackageImports" not in content:
                    suggestions.append("Add experimental.optimizePackageImports for lucide-react, @heroicons/react")

                # Check for transpilePackages
                if "transpilePackages" not in content and "swc" not in content:
                    suggestions.append("Consider transpilePackages for monorepo packages")

                return {
                    "found": True,
                    "path": str(config_path),
                    "suggestions": suggestions
                }
            except Exception:
                pass

    return {
        "found": False,
        "suggestions": ["Create next.config.js with image and bundle optimizations"]
    }


def analyze_imports(project_dir: Path) -> Dict:
    """Analyze import patterns in source files."""
    issues = []
    src_dirs = [project_dir / "src", project_dir / "app", project_dir / "pages"]

    patterns_to_check = [
        (r"import\s+\*\s+as\s+\w+\s+from\s+['\"]lodash['\"]", "Avoid import * from lodash, use individual imports"),
        (r"import\s+moment\s+from\s+['\"]moment['\"]", "Consider replacing moment with date-fns or dayjs"),
        (r"import\s+\{\s*\w+(?:,\s*\w+){5,}\s*\}\s+from\s+['\"]react-icons", "Import icons from specific icon sets (react-icons/fa)"),
    ]

    files_checked = 0
    for src_dir in src_dirs:
        if not src_dir.exists():
            continue

        for ext in ["*.ts", "*.tsx", "*.js", "*.jsx"]:
            for file_path in src_dir.glob(f"**/{ext}"):
                if "node_modules" in str(file_path):
                    continue

                files_checked += 1
                try:
                    content = file_path.read_text()
                    for pattern, message in patterns_to_check:
                        if re.search(pattern, content):
                            issues.append({
                                "file": str(file_path.relative_to(project_dir)),
                                "issue": message
                            })
                except Exception:
                    continue

    return {
        "files_checked": files_checked,
        "issues": issues
    }


def calculate_score(analysis: Dict) -> Tuple[int, str]:
    """Calculate bundle health score."""
    score = 100

    # Deduct for heavy dependencies
    score -= len(analysis["dependencies"]["issues"]) * 10

    # Deduct for dev deps in production
    score -= len([w for w in analysis["dependencies"]["warnings"]
                  if w.get("type") == "dev_in_production"]) * 5

    # Deduct for import issues
    score -= len(analysis.get("imports", {}).get("issues", [])) * 3

    # Deduct for missing Next.js optimizations
    if not analysis.get("nextjs", {}).get("found", True):
        score -= 10

    score = max(0, min(100, score))

    if score >= 90:
        grade = "A"
    elif score >= 80:
        grade = "B"
    elif score >= 70:
        grade = "C"
    elif score >= 60:
        grade = "D"
    else:
        grade = "F"

    return score, grade


def print_report(analysis: Dict) -> None:
    """Print human-readable report."""
    score, grade = calculate_score(analysis)

    print("=" * 60)
    print("FRONTEND BUNDLE ANALYSIS REPORT")
    print("=" * 60)
    print(f"\nBundle Health Score: {score}/100 ({grade})")

    deps = analysis["dependencies"]
    print(f"\nDependencies: {deps['total_dependencies']} production, {deps['total_dev_dependencies']} dev")

    # Heavy dependencies
    if deps["issues"]:
        print("\n--- HEAVY DEPENDENCIES ---")
        for issue in deps["issues"]:
            print(f"\n  {issue['package']} ({issue['size']})")
            print(f"    Reason: {issue['reason']}")
            print(f"    Alternative: {issue['alternative']}")

    # Warnings
    if deps["warnings"]:
        print("\n--- WARNINGS ---")
        for warning in deps["warnings"]:
            if "package" in warning:
                print(f"  - {warning['package']}: {warning['message']}")
            else:
                print(f"  - {warning['message']}")

    # Optimizations
    if deps["optimizations"]:
        print("\n--- OPTIMIZATION TIPS ---")
        for opt in deps["optimizations"]:
            print(f"  - {opt['package']}: {opt['tip']}")

    # Next.js config
    if "nextjs" in analysis:
        nextjs = analysis["nextjs"]
        if nextjs.get("suggestions"):
            print("\n--- NEXT.JS CONFIG ---")
            for suggestion in nextjs["suggestions"]:
                print(f"  - {suggestion}")

    # Import issues
    if analysis.get("imports", {}).get("issues"):
        print("\n--- IMPORT ISSUES ---")
        for issue in analysis["imports"]["issues"][:10]:  # Limit to 10
            print(f"  - {issue['file']}: {issue['issue']}")

    # Summary
    print("\n--- RECOMMENDATIONS ---")
    if score >= 90:
        print("  Bundle is well-optimized!")
    elif deps["issues"]:
        print("  1. Replace heavy dependencies with lighter alternatives")
    if deps["warnings"]:
        print("  2. Move dev-only packages to devDependencies")
    if deps["optimizations"]:
        print("  3. Apply import optimizations for tree-shaking")

    print("\n" + "=" * 60)


def main():
    parser = argparse.ArgumentParser(
        description="Analyze frontend project for bundle optimization opportunities"
    )
    parser.add_argument(
        "project_dir",
        nargs="?",
        default=".",
        help="Project directory to analyze (default: current directory)"
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Output in JSON format"
    )
    parser.add_argument(
        "--verbose", "-v",
        action="store_true",
        help="Include detailed import analysis"
    )

    args = parser.parse_args()
    project_dir = Path(args.project_dir).resolve()

    if not project_dir.exists():
        print(f"Error: Directory not found: {project_dir}", file=sys.stderr)
        sys.exit(1)

    package_json = load_package_json(project_dir)
    if not package_json:
        print("Error: No valid package.json found", file=sys.stderr)
        sys.exit(1)

    analysis = {
        "project": str(project_dir),
        "dependencies": analyze_dependencies(package_json),
        "nextjs": check_nextjs_config(project_dir)
    }

    if args.verbose:
        analysis["imports"] = analyze_imports(project_dir)

    analysis["score"], analysis["grade"] = calculate_score(analysis)

    if args.json:
        print(json.dumps(analysis, indent=2))
    else:
        print_report(analysis)


if __name__ == "__main__":
    main()
