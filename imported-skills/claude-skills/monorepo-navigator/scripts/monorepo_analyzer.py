#!/usr/bin/env python3
"""Detect monorepo tooling, workspaces, and internal dependency graph."""

from __future__ import annotations

import argparse
import glob
import json
import os
from pathlib import Path
from typing import Dict, List, Set


def load_json(path: Path) -> Dict:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {}


def detect_repo_type(root: Path) -> List[str]:
    detected: List[str] = []
    if (root / "turbo.json").exists():
        detected.append("Turborepo")
    if (root / "nx.json").exists():
        detected.append("Nx")
    if (root / "pnpm-workspace.yaml").exists():
        detected.append("pnpm-workspaces")
    if (root / "lerna.json").exists():
        detected.append("Lerna")

    pkg = load_json(root / "package.json")
    if "workspaces" in pkg and "npm-workspaces" not in detected:
        detected.append("npm-workspaces")
    return detected


def parse_pnpm_workspace(root: Path) -> List[str]:
    workspace_file = root / "pnpm-workspace.yaml"
    if not workspace_file.exists():
        return []

    patterns: List[str] = []
    in_packages = False
    for line in workspace_file.read_text(encoding="utf-8", errors="ignore").splitlines():
        stripped = line.strip()
        if stripped.startswith("packages:"):
            in_packages = True
            continue
        if in_packages and stripped.startswith("-"):
            item = stripped[1:].strip().strip('"').strip("'")
            if item:
                patterns.append(item)
        elif in_packages and stripped and not stripped.startswith("#") and not stripped.startswith("-"):
            in_packages = False
    return patterns


def parse_package_workspaces(root: Path) -> List[str]:
    pkg = load_json(root / "package.json")
    workspaces = pkg.get("workspaces")
    if isinstance(workspaces, list):
        return [str(item) for item in workspaces]
    if isinstance(workspaces, dict) and isinstance(workspaces.get("packages"), list):
        return [str(item) for item in workspaces["packages"]]
    return []


def expand_workspace_patterns(root: Path, patterns: List[str]) -> List[Path]:
    paths: Set[Path] = set()
    for pattern in patterns:
        for match in glob.glob(str(root / pattern)):
            p = Path(match)
            if p.is_dir() and (p / "package.json").exists():
                paths.add(p.resolve())
    return sorted(paths)


def load_workspace_packages(workspaces: List[Path]) -> Dict[str, Dict]:
    packages: Dict[str, Dict] = {}
    for ws in workspaces:
        data = load_json(ws / "package.json")
        name = data.get("name") or ws.name
        packages[name] = {
            "path": str(ws),
            "dependencies": data.get("dependencies", {}),
            "devDependencies": data.get("devDependencies", {}),
            "peerDependencies": data.get("peerDependencies", {}),
        }
    return packages


def build_dependency_graph(packages: Dict[str, Dict]) -> Dict[str, List[str]]:
    package_names = set(packages.keys())
    graph: Dict[str, List[str]] = {}
    for name, meta in packages.items():
        deps: Set[str] = set()
        for section in ("dependencies", "devDependencies", "peerDependencies"):
            dep_map = meta.get(section, {})
            if isinstance(dep_map, dict):
                for dep_name in dep_map.keys():
                    if dep_name in package_names:
                        deps.add(dep_name)
        graph[name] = sorted(deps)
    return graph


def format_tree_paths(root: Path, workspaces: List[Path]) -> List[str]:
    out: List[str] = []
    for ws in workspaces:
        out.append(str(ws.relative_to(root)))
    return out


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Analyze monorepo type, workspaces, and internal dependency graph.")
    parser.add_argument("path", help="Monorepo root path")
    parser.add_argument("--json", action="store_true", help="Output JSON")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = Path(args.path).expanduser().resolve()
    if not root.exists() or not root.is_dir():
        raise SystemExit(f"Path is not a directory: {root}")

    types = detect_repo_type(root)
    patterns = parse_pnpm_workspace(root)
    if not patterns:
        patterns = parse_package_workspaces(root)

    workspaces = expand_workspace_patterns(root, patterns)
    packages = load_workspace_packages(workspaces)
    graph = build_dependency_graph(packages)

    report = {
        "root": str(root),
        "detected_types": types,
        "workspace_patterns": patterns,
        "workspace_paths": format_tree_paths(root, workspaces),
        "package_count": len(packages),
        "dependency_graph": graph,
    }

    if args.json:
        print(json.dumps(report, indent=2))
    else:
        print("Monorepo Analysis")
        print(f"Root: {report['root']}")
        print(f"Detected: {', '.join(types) if types else 'none'}")
        print(f"Workspace patterns: {', '.join(patterns) if patterns else 'none'}")
        print("")
        print("Workspaces")
        for ws in report["workspace_paths"]:
            print(f"- {ws}")
        if not report["workspace_paths"]:
            print("- none detected")
        print("")
        print("Internal dependency graph")
        for pkg, deps in graph.items():
            print(f"- {pkg} -> {', '.join(deps) if deps else '(no internal deps)'}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
