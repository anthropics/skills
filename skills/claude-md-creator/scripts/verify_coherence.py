#!/usr/bin/env python3
"""
Phase 2: Verify extracted claims against the actual codebase.

Takes claims.json from Phase 1 and checks each claim against the real project:
commands in package.json, paths on filesystem, frameworks in dependencies, etc.

Usage:
    python -m scripts.verify_coherence <claims.json> <project-root> [--output <path>]
"""

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path


# ---------------------------------------------------------------------------
# Dependency file parsers
# ---------------------------------------------------------------------------


def parse_package_json(project_root: Path) -> dict:
    """Parse package.json for scripts and dependencies."""
    pkg_path = project_root / "package.json"
    if not pkg_path.exists():
        return {}
    try:
        data = json.loads(pkg_path.read_text(encoding="utf-8"))
        return {
            "scripts": data.get("scripts", {}),
            "dependencies": {
                **data.get("dependencies", {}),
                **data.get("devDependencies", {}),
                **data.get("peerDependencies", {}),
            },
            "type": "node",
        }
    except (json.JSONDecodeError, OSError):
        return {}


def parse_pyproject_toml(project_root: Path) -> dict:
    """Parse pyproject.toml for dependencies and scripts."""
    toml_path = project_root / "pyproject.toml"
    if not toml_path.exists():
        return {}
    try:
        # Try tomllib (Python 3.11+) or fall back to regex
        try:
            import tomllib
            data = tomllib.loads(toml_path.read_text(encoding="utf-8"))
        except ImportError:
            # Fallback: simple regex extraction
            content = toml_path.read_text(encoding="utf-8")
            deps = set(re.findall(r'^\s*"?(\w[\w-]*)"?\s*[=><]', content, re.MULTILINE))
            return {"dependencies": {d: "*" for d in deps}, "scripts": {}, "type": "python"}

        deps = {}
        # Poetry
        for section in ["tool.poetry.dependencies", "tool.poetry.dev-dependencies"]:
            parts = section.split(".")
            d = data
            for p in parts:
                d = d.get(p, {})
            if isinstance(d, dict):
                deps.update(d)
        # PEP 621
        for dep_str in data.get("project", {}).get("dependencies", []):
            name = re.split(r"[><=!\[;]", dep_str)[0].strip()
            if name:
                deps[name.lower()] = "*"

        scripts = {}
        for section in ["tool.poetry.scripts", "project.scripts"]:
            parts = section.split(".")
            d = data
            for p in parts:
                d = d.get(p, {})
            if isinstance(d, dict):
                scripts.update(d)

        return {"dependencies": deps, "scripts": scripts, "type": "python"}
    except Exception:
        return {}


def parse_requirements_txt(project_root: Path) -> dict:
    """Parse requirements.txt for dependencies."""
    req_path = project_root / "requirements.txt"
    if not req_path.exists():
        return {}
    try:
        content = req_path.read_text(encoding="utf-8")
        deps = {}
        for line in content.splitlines():
            line = line.strip()
            if line and not line.startswith("#") and not line.startswith("-"):
                name = re.split(r"[><=!\[;]", line)[0].strip()
                if name:
                    deps[name.lower()] = "*"
        return {"dependencies": deps, "scripts": {}, "type": "python"}
    except OSError:
        return {}


def parse_cargo_toml(project_root: Path) -> dict:
    """Parse Cargo.toml for dependencies."""
    cargo_path = project_root / "Cargo.toml"
    if not cargo_path.exists():
        return {}
    try:
        content = cargo_path.read_text(encoding="utf-8")
        deps = set(re.findall(r'^\s*(\w[\w-]*)\s*=', content, re.MULTILINE))
        return {"dependencies": {d: "*" for d in deps}, "scripts": {}, "type": "rust"}
    except OSError:
        return {}


def parse_go_mod(project_root: Path) -> dict:
    """Parse go.mod for dependencies."""
    mod_path = project_root / "go.mod"
    if not mod_path.exists():
        return {}
    try:
        content = mod_path.read_text(encoding="utf-8")
        deps = {}
        for match in re.finditer(r"^\s+([\w./-]+)\s+v", content, re.MULTILINE):
            parts = match.group(1).split("/")
            deps[parts[-1].lower()] = "*"
        return {"dependencies": deps, "scripts": {}, "type": "go"}
    except OSError:
        return {}


def parse_makefile(project_root: Path) -> dict:
    """Parse Makefile for target names."""
    makefile = project_root / "Makefile"
    if not makefile.exists():
        return {}
    try:
        content = makefile.read_text(encoding="utf-8")
        targets = set(re.findall(r"^([\w-]+)\s*:", content, re.MULTILINE))
        return {"scripts": {t: t for t in targets}, "dependencies": {}, "type": "make"}
    except OSError:
        return {}


def parse_gemfile(project_root: Path) -> dict:
    """Parse Gemfile for dependencies."""
    gemfile = project_root / "Gemfile"
    if not gemfile.exists():
        return {}
    try:
        content = gemfile.read_text(encoding="utf-8")
        deps = {}
        for match in re.finditer(r"""gem\s+['"](\w[\w-]*)['"]""", content):
            deps[match.group(1).lower()] = "*"
        return {"dependencies": deps, "scripts": {}, "type": "ruby"}
    except OSError:
        return {}


def get_project_info(project_root: Path) -> dict:
    """Gather all project dependency and script information."""
    info = {"scripts": {}, "dependencies": {}, "types": []}

    parsers = [
        parse_package_json,
        parse_pyproject_toml,
        parse_requirements_txt,
        parse_cargo_toml,
        parse_go_mod,
        parse_makefile,
        parse_gemfile,
    ]

    for parser in parsers:
        result = parser(project_root)
        if result:
            info["scripts"].update(result.get("scripts", {}))
            info["dependencies"].update(result.get("dependencies", {}))
            if result.get("type"):
                info["types"].append(result["type"])

    return info


# ---------------------------------------------------------------------------
# Verifiers — one per claim type
# ---------------------------------------------------------------------------


def verify_command(claim: dict, project_root: Path, project_info: dict) -> dict:
    """Verify that a CLI command exists in the project."""
    command = claim["extracted"]["command"]
    tokens = command.split()
    base_cmd = tokens[0]
    sub_cmd = tokens[1] if len(tokens) > 1 else None

    # Check package.json scripts (npm/pnpm/yarn run X or npm/pnpm/yarn X)
    if base_cmd in ("npm", "pnpm", "yarn", "bun"):
        script_name = None
        if sub_cmd == "run" and len(tokens) > 2:
            script_name = tokens[2]
        elif sub_cmd and sub_cmd not in ("install", "add", "remove", "init", "create", "dlx", "exec", "i"):
            script_name = sub_cmd

        if script_name:
            if script_name in project_info.get("scripts", {}):
                return {
                    "status": "verified",
                    "evidence": f"Found in scripts: \"{script_name}\": \"{project_info['scripts'][script_name]}\"",
                    "confidence": 1.0,
                }
            else:
                available = list(project_info.get("scripts", {}).keys())
                return {
                    "status": "stale",
                    "evidence": f"Script '{script_name}' not found in package.json. Available: {available[:10]}",
                    "confidence": 0.0,
                    "suggestion": f"Check if '{script_name}' was renamed or removed",
                }

    # Check make targets
    if base_cmd == "make" and sub_cmd:
        if sub_cmd in project_info.get("scripts", {}):
            return {
                "status": "verified",
                "evidence": f"Found Makefile target: {sub_cmd}",
                "confidence": 1.0,
            }

    # Check if base command is available on system
    if shutil.which(base_cmd):
        return {
            "status": "verified",
            "evidence": f"Command '{base_cmd}' is available on PATH",
            "confidence": 0.7,
        }

    return {
        "status": "unverifiable",
        "evidence": f"Cannot verify command '{command}' — not in project scripts and not on PATH",
        "confidence": 0.3,
    }


def _resolve_alias_path(path_str: str, project_root: Path) -> Path | None:
    """Resolve @/ alias paths by checking tsconfig.json and common source dirs."""
    if not path_str.startswith("@/"):
        return None

    relative = path_str[2:]  # strip @/

    # Try common source directories for @/ alias
    candidates = ["src", ".", "app", "lib"]
    seen_candidates = set(candidates)

    # Also try to read tsconfig.json for paths configuration
    for tsconfig_name in ("tsconfig.json", "tsconfig.app.json"):
        tsconfig_path = project_root / tsconfig_name
        if tsconfig_path.exists():
            try:
                # Strip comments for JSON parsing
                text = tsconfig_path.read_text(encoding="utf-8")
                text = re.sub(r"//.*$", "", text, flags=re.MULTILINE)
                text = re.sub(r"/\*.*?\*/", "", text, flags=re.DOTALL)
                config = json.loads(text)
                paths = config.get("compilerOptions", {}).get("paths", {})
                for alias_pattern, target_patterns in paths.items():
                    if alias_pattern.startswith("@/"):
                        for target in target_patterns:
                            base = target.replace("/*", "").replace("*", "")
                            if base and base not in seen_candidates:
                                seen_candidates.add(base)
                                candidates.insert(0, base)
            except (json.JSONDecodeError, OSError):
                pass

    for base_dir in candidates:
        resolved = project_root / base_dir / relative
        if resolved.exists():
            return resolved
        # Try with common extensions
        for ext in (".ts", ".tsx", ".js", ".jsx"):
            if (project_root / base_dir / (relative + ext)).exists():
                return project_root / base_dir / (relative + ext)
            if (project_root / base_dir / relative / ("index" + ext)).exists():
                return project_root / base_dir / relative / ("index" + ext)

    return None


def verify_path(claim: dict, project_root: Path, project_info: dict) -> dict:
    """Verify that a file/directory path exists."""
    path_str = claim["extracted"]["path"]
    # Remove leading ./ and trailing glob patterns
    clean_path = re.sub(r"[*{}\[\]]+.*$", "", path_str.lstrip("./"))

    # Handle @/ alias paths
    if clean_path.startswith("@/"):
        resolved = _resolve_alias_path(clean_path, project_root)
        if resolved and resolved.exists():
            if resolved.is_dir():
                file_count = sum(1 for _ in resolved.iterdir())
                return {
                    "status": "verified",
                    "evidence": f"Alias path resolved: {resolved.relative_to(project_root)} ({file_count} entries)",
                    "confidence": 1.0,
                }
            else:
                return {
                    "status": "verified",
                    "evidence": f"Alias path resolved: {resolved.relative_to(project_root)} ({resolved.stat().st_size} bytes)",
                    "confidence": 1.0,
                }

    full_path = project_root / clean_path

    if full_path.exists():
        if full_path.is_dir():
            file_count = sum(1 for _ in full_path.iterdir())
            return {
                "status": "verified",
                "evidence": f"Directory exists with {file_count} entries",
                "confidence": 1.0,
            }
        else:
            return {
                "status": "verified",
                "evidence": f"File exists ({full_path.stat().st_size} bytes)",
                "confidence": 1.0,
            }

    # For short relative paths (e.g., _common/StatusBar.tsx, entity/),
    # try finding them anywhere in the project tree
    if not clean_path.startswith("/") and ".." not in clean_path and len(Path(clean_path).parts) <= 3:
        search_name = clean_path.rstrip("/")
        # Use -name for simple names, -path for multi-segment paths
        if "/" in search_name:
            find_args = ["-path", f"*/{search_name}"]
        else:
            find_args = ["-name", search_name]
        try:
            result = subprocess.run(
                ["find", str(project_root), "-maxdepth", "8"] + find_args,
                capture_output=True, text=True, timeout=5,
            )
            matches = [l for l in result.stdout.strip().splitlines() if l]
            if matches:
                rel = Path(matches[0]).relative_to(project_root)
                return {
                    "status": "verified",
                    "evidence": f"Found at {rel}" + (f" (+{len(matches)-1} more)" if len(matches) > 1 else ""),
                    "confidence": 0.8,
                }
        except (subprocess.TimeoutExpired, OSError):
            pass

    # Try to find similar paths
    parent = full_path.parent
    if parent.exists():
        siblings = [p.name for p in parent.iterdir()]
        target_name = full_path.name
        similar = [s for s in siblings if target_name.lower() in s.lower() or s.lower() in target_name.lower()]
        if similar:
            return {
                "status": "stale",
                "evidence": f"Path '{clean_path}' not found. Similar in {parent.relative_to(project_root)}/: {similar[:5]}",
                "confidence": 0.0,
                "suggestion": f"Check if path was renamed. Similar: {similar[:3]}",
            }

    # Check if any part of the path exists
    parts = Path(clean_path).parts
    existing_depth = 0
    check_path = project_root
    for part in parts:
        check_path = check_path / part
        if check_path.exists():
            existing_depth += 1
        else:
            break

    if existing_depth > 0:
        existing = "/".join(parts[:existing_depth])
        return {
            "status": "stale",
            "evidence": f"Path '{clean_path}' not found. Exists up to: {existing}/",
            "confidence": 0.0,
            "suggestion": f"Directory '{clean_path}' does not exist. Partial match: {existing}/",
        }

    return {
        "status": "stale",
        "evidence": f"Path '{clean_path}' does not exist",
        "confidence": 0.0,
        "suggestion": f"Remove or update reference to '{clean_path}'",
    }


def verify_framework(claim: dict, project_root: Path, project_info: dict) -> dict:
    """Verify that a framework/library is in project dependencies."""
    framework = claim["extracted"]["framework"]
    deps = project_info.get("dependencies", {})

    # Normalize: some frameworks have different package names
    aliases = {
        "next.js": ["next"],
        "next": ["next"],
        "nextjs": ["next"],
        "react": ["react"],
        "tailwind": ["tailwindcss"],
        "tailwindcss": ["tailwindcss"],
        "prisma": ["prisma", "@prisma/client"],
        "drizzle": ["drizzle-orm"],
        "jest": ["jest", "@jest/core"],
        "vitest": ["vitest"],
        "playwright": ["playwright", "@playwright/test"],
        "storybook": ["storybook", "@storybook/react"],
        "eslint": ["eslint"],
        "prettier": ["prettier"],
        "emotion": ["@emotion/react", "@emotion/styled"],
        "styled-components": ["styled-components"],
        "testing-library": ["@testing-library/react"],
        "msw": ["msw"],
        "zod": ["zod"],
        "django": ["django"],
        "flask": ["flask"],
        "fastapi": ["fastapi"],
        "pytest": ["pytest"],
        "rails": ["rails"],
    }

    package_names = aliases.get(framework.lower(), [framework.lower()])

    deps_lower = {k.lower(): k for k in deps}
    for pkg in package_names:
        if pkg.lower() in deps_lower:
            original_key = deps_lower[pkg.lower()]
            return {
                "status": "verified",
                "evidence": f"Found '{original_key}' in project dependencies",
                "confidence": 1.0,
            }

    # Check config file if referenced
    config_path = claim["extracted"].get("config_path")
    if config_path and (project_root / config_path).exists():
        return {
            "status": "verified",
            "evidence": f"Config file '{config_path}' exists (package may be transitive dependency)",
            "confidence": 0.8,
        }

    return {
        "status": "stale",
        "evidence": f"'{framework}' not found in project dependencies. Checked: {package_names}",
        "confidence": 0.0,
        "suggestion": f"Remove '{framework}' reference or add it as a dependency",
    }


def verify_convention(claim: dict, project_root: Path, project_info: dict) -> dict:
    """Verify a convention by sampling code files."""
    # Convention verification requires understanding the rule semantically.
    # The script does basic checks; the coherence_checker agent enriches.
    return {
        "status": "unverifiable",
        "evidence": "Convention claims require agent-level semantic analysis for full verification",
        "confidence": 0.5,
        "note": "The coherence_checker agent will enrich this result",
    }


def verify_naming_pattern(claim: dict, project_root: Path, project_info: dict) -> dict:
    """Verify naming conventions against actual file/identifier names."""
    return {
        "status": "unverifiable",
        "evidence": "Naming pattern verification requires sampling project files",
        "confidence": 0.5,
        "note": "The coherence_checker agent will enrich this result",
    }


def verify_env_reference(claim: dict, project_root: Path, project_info: dict) -> dict:
    """Verify environment variable references."""
    var_name = claim["extracted"]["variable"]

    # Check .env.example, .env.local.example, .env.sample
    env_files = [".env.example", ".env.local.example", ".env.sample", ".env"]
    for env_file in env_files:
        env_path = project_root / env_file
        if env_path.exists():
            content = env_path.read_text(encoding="utf-8")
            if var_name in content:
                return {
                    "status": "verified",
                    "evidence": f"Found '{var_name}' in {env_file}",
                    "confidence": 1.0,
                }

    # Check if it's a prefix pattern (like NEXT_PUBLIC_*)
    if var_name.endswith("_") or "*" in var_name:
        prefix = var_name.rstrip("_*")
        for env_file in env_files:
            env_path = project_root / env_file
            if env_path.exists():
                content = env_path.read_text(encoding="utf-8")
                if prefix in content:
                    return {
                        "status": "verified",
                        "evidence": f"Found variables with prefix '{prefix}' in {env_file}",
                        "confidence": 0.8,
                    }

    return {
        "status": "unverifiable",
        "evidence": f"Cannot verify env var '{var_name}' — no .env example files found",
        "confidence": 0.3,
    }


# ---------------------------------------------------------------------------
# Main verification pipeline
# ---------------------------------------------------------------------------

VERIFIERS = {
    "command": verify_command,
    "path_reference": verify_path,
    "framework_reference": verify_framework,
    "convention": verify_convention,
    "naming_pattern": verify_naming_pattern,
    "env_reference": verify_env_reference,
}


def verify_coherence(claims_data: dict, project_root: Path) -> dict:
    """Verify all claims against the codebase."""
    project_info = get_project_info(project_root)
    results = []

    for claim in claims_data["claims"]:
        claim_type = claim["type"]

        # Skip non-testable claims
        if not claim.get("testable", True):
            results.append({
                "claim_id": claim["id"],
                "type": claim_type,
                "claim_text": claim["raw_text"],
                "status": "not_applicable",
                "evidence": claim["extracted"].get("issue", "Not testable"),
                "confidence": 0.0,
            })
            continue

        verifier = VERIFIERS.get(claim_type)
        if verifier:
            result = verifier(claim, project_root, project_info)
            results.append({
                "claim_id": claim["id"],
                "type": claim_type,
                "claim_text": claim["raw_text"],
                **result,
            })
        else:
            results.append({
                "claim_id": claim["id"],
                "type": claim_type,
                "claim_text": claim["raw_text"],
                "status": "unverifiable",
                "evidence": f"No verifier for claim type '{claim_type}'",
                "confidence": 0.0,
            })

    # Compute summary
    testable = [r for r in results if r["status"] != "not_applicable"]
    verified = sum(1 for r in testable if r["status"] == "verified")
    stale = sum(1 for r in testable if r["status"] == "stale")
    partial = sum(1 for r in testable if r["status"] == "partial")
    unverifiable = sum(1 for r in testable if r["status"] == "unverifiable")

    verifiable_count = len(testable) - unverifiable
    coherence_score = round((verified / verifiable_count * 100), 1) if verifiable_count > 0 else 0

    return {
        "project_root": str(project_root),
        "project_info": {
            "ecosystems": project_info.get("types", []),
            "scripts_count": len(project_info.get("scripts", {})),
            "dependencies_count": len(project_info.get("dependencies", {})),
        },
        "total_claims": len(claims_data["claims"]),
        "testable_claims": len(testable),
        "verified": verified,
        "stale": stale,
        "partial": partial,
        "unverifiable": unverifiable,
        "coherence_score": coherence_score,
        "results": results,
    }


def main():
    parser = argparse.ArgumentParser(description="Verify CLAUDE.md claims against codebase")
    parser.add_argument("claims_json", type=Path, help="Path to claims.json")
    parser.add_argument("project_root", type=Path, help="Project root directory")
    parser.add_argument("--output", type=Path, default=None)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()

    claims_data = json.loads(args.claims_json.read_text(encoding="utf-8"))
    result = verify_coherence(claims_data, args.project_root)

    output_json = json.dumps(result, indent=2 if args.pretty else None, ensure_ascii=False)

    if args.output:
        args.output.write_text(output_json, encoding="utf-8")
        print(f"Coherence report → {args.output}")
        print(f"Score: {result['coherence_score']}/100 "
              f"({result['verified']} verified, {result['stale']} stale, {result['unverifiable']} unverifiable)")
    else:
        print(output_json)


if __name__ == "__main__":
    main()
