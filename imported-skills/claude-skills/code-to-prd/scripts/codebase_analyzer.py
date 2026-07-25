#!/usr/bin/env python3
"""Analyze any codebase (frontend, backend, or fullstack) and extract routes, APIs, models, and structure.

Supports: React, Vue, Angular, Svelte, Next.js, Nuxt, NestJS, Express, Django, FastAPI, Flask.
Stdlib only — no third-party dependencies. Outputs JSON for downstream PRD generation.

Usage:
    python3 codebase_analyzer.py /path/to/project
    python3 codebase_analyzer.py /path/to/project --output prd-analysis.json
    python3 codebase_analyzer.py /path/to/project --format markdown
"""

import argparse
import json
import os
import re
from collections import defaultdict
from pathlib import Path
from typing import Any, Dict, List, Optional, Set, Tuple

IGNORED_DIRS = {
    ".git", "node_modules", ".next", "dist", "build", "coverage",
    "venv", ".venv", "__pycache__", ".nuxt", ".output", ".cache",
    ".turbo", ".vercel", "out", "storybook-static",
    ".tox", ".mypy_cache", ".pytest_cache", "htmlcov", "staticfiles",
    "media", "migrations", "egg-info",
}

FRAMEWORK_SIGNALS = {
    "react": ["react", "react-dom"],
    "next": ["next"],
    "vue": ["vue"],
    "nuxt": ["nuxt"],
    "angular": ["@angular/core"],
    "svelte": ["svelte"],
    "sveltekit": ["@sveltejs/kit"],
    "solid": ["solid-js"],
    "astro": ["astro"],
    "remix": ["@remix-run/react"],
    "nestjs": ["@nestjs/core"],
    "express": ["express"],
    "fastify": ["fastify"],
}

# Python backend frameworks detected via project files (no package.json)
PYTHON_FRAMEWORK_FILES = {
    "django": ["manage.py", "settings.py"],
    "fastapi": ["main.py"],  # confirmed via imports
    "flask": ["app.py"],      # confirmed via imports
}

ROUTE_FILE_PATTERNS = [
    "**/router.{ts,tsx,js,jsx}",
    "**/routes.{ts,tsx,js,jsx}",
    "**/routing.{ts,tsx,js,jsx}",
    "**/app-routing*.{ts,tsx,js,jsx}",
]

ROUTE_DIR_PATTERNS = [
    "pages", "views", "routes", "app",
    "src/pages", "src/views", "src/routes", "src/app",
]

API_DIR_PATTERNS = [
    "api", "services", "requests", "endpoints", "client",
    "src/api", "src/services", "src/requests",
]

STATE_DIR_PATTERNS = [
    "store", "stores", "models", "context", "state",
    "src/store", "src/stores", "src/models", "src/context",
]

I18N_DIR_PATTERNS = [
    "locales", "i18n", "lang", "translations", "messages",
    "src/locales", "src/i18n", "src/lang",
]

# Backend-specific directory patterns
CONTROLLER_DIR_PATTERNS = [
    "controllers", "src/controllers", "src/modules",
]

MODEL_DIR_PATTERNS = [
    "models", "entities", "src/entities", "src/models",
]

DTO_DIR_PATTERNS = [
    "dto", "dtos", "src/dto", "serializers",
]

MOCK_SIGNALS = [
    r"setTimeout\s*\(.*\breturn\b",
    r"Promise\.resolve\s*\(",
    r"\.mock\.",
    r"__mocks__",
    r"mockData",
    r"mock[A-Z]",
    r"faker\.",
    r"fixtures?/",
]

REAL_API_SIGNALS = [
    r"\baxios\b",
    r"\bfetch\s*\(",
    r"httpGet|httpPost|httpPut|httpDelete|httpPatch",
    r"\.get\s*\(\s*['\"`/]",
    r"\.post\s*\(\s*['\"`/]",
    r"\.put\s*\(\s*['\"`/]",
    r"\.delete\s*\(\s*['\"`/]",
    r"\.patch\s*\(\s*['\"`/]",
    r"useSWR|useQuery|useMutation",
    r"\$http\.",
    r"this\.http\.",
]

ROUTE_PATTERNS = [
    # React Router
    r'<Route\s+[^>]*path\s*=\s*["\']([^"\']+)["\']',
    r'path\s*:\s*["\']([^"\']+)["\']',
    # Vue Router
    r'path\s*:\s*["\']([^"\']+)["\']',
    # Angular
    r'path\s*:\s*["\']([^"\']+)["\']',
]

API_PATH_PATTERNS = [
    r'["\'](?:GET|POST|PUT|DELETE|PATCH)["\'].*?["\'](/[a-zA-Z0-9/_\-:{}]+)["\']',
    r'(?:get|post|put|delete|patch)\s*\(\s*["\'](/[a-zA-Z0-9/_\-:{}]+)["\']',
    r'(?:url|path|endpoint|baseURL)\s*[:=]\s*["\'](/[a-zA-Z0-9/_\-:{}]+)["\']',
    r'fetch\s*\(\s*[`"\'](?:https?://[^/]+)?(/[a-zA-Z0-9/_\-:{}]+)',
]

COMPONENT_EXTENSIONS = {".tsx", ".jsx", ".vue", ".svelte", ".astro"}
CODE_EXTENSIONS = {".ts", ".tsx", ".js", ".jsx", ".vue", ".svelte", ".astro", ".py"}

# NestJS decorator patterns
NEST_ROUTE_PATTERNS = [
    r"@(?:Get|Post|Put|Delete|Patch|Head|Options|All)\s*\(\s*['\"]([^'\"]*)['\"]",
    r"@Controller\s*\(\s*['\"]([^'\"]*)['\"]",
]

# Django URL patterns
DJANGO_ROUTE_PATTERNS = [
    r"path\s*\(\s*['\"]([^'\"]+)['\"]",
    r"url\s*\(\s*r?['\"]([^'\"]+)['\"]",
    r"register\s*\(\s*r?['\"]([^'\"]+)['\"]",
]

# Django/Python model patterns
PYTHON_MODEL_PATTERNS = [
    r"class\s+(\w+)\s*\(.*?models\.Model\)",
    r"class\s+(\w+)\s*\(.*?BaseModel\)",  # Pydantic
]

# NestJS entity/DTO patterns
NEST_MODEL_PATTERNS = [
    r"@Entity\s*\(.*?\)\s*(?:export\s+)?class\s+(\w+)",
    r"class\s+(\w+(?:Dto|DTO|Entity|Schema))\b",
]


def detect_framework(project_root: Path) -> Dict[str, Any]:
    """Detect framework from package.json (Node.js) or project files (Python)."""
    detected = []
    all_deps = {}
    pkg_name = ""
    pkg_version = ""

    # Node.js detection via package.json
    pkg_path = project_root / "package.json"
    if pkg_path.exists():
        try:
            with open(pkg_path) as f:
                pkg = json.load(f)
            pkg_name = pkg.get("name", "")
            pkg_version = pkg.get("version", "")
            for key in ("dependencies", "devDependencies", "peerDependencies"):
                all_deps.update(pkg.get(key, {}))
            for framework, signals in FRAMEWORK_SIGNALS.items():
                if any(s in all_deps for s in signals):
                    detected.append(framework)
        except (json.JSONDecodeError, IOError):
            pass

    # Python backend detection via project files and imports
    if (project_root / "manage.py").exists():
        detected.append("django")
    if (project_root / "requirements.txt").exists() or (project_root / "pyproject.toml").exists():
        for req_file in ["requirements.txt", "pyproject.toml", "setup.py", "Pipfile"]:
            req_path = project_root / req_file
            if req_path.exists():
                try:
                    content = req_path.read_text(errors="replace").lower()
                    if "django" in content and "django" not in detected:
                        detected.append("django")
                    if "fastapi" in content:
                        detected.append("fastapi")
                    if "flask" in content and "flask" not in detected:
                        detected.append("flask")
                except IOError:
                    pass

    # Prefer specific over generic
    priority = [
        "sveltekit", "next", "nuxt", "remix", "astro",  # fullstack JS
        "nestjs", "express", "fastify",                   # backend JS
        "django", "fastapi", "flask",                     # backend Python
        "angular", "svelte", "vue", "react", "solid",     # frontend JS
    ]
    framework = "unknown"
    for fw in priority:
        if fw in detected:
            framework = fw
            break

    return {
        "framework": framework,
        "name": pkg_name or project_root.name,
        "version": pkg_version,
        "detected_frameworks": detected,
        "dependency_count": len(all_deps),
        "key_deps": {k: v for k, v in all_deps.items()
                     if any(s in k for s in ["router", "redux", "vuex", "pinia", "zustand",
                                              "mobx", "recoil", "jotai", "tanstack", "swr",
                                              "axios", "tailwind", "material", "ant",
                                              "chakra", "shadcn", "i18n", "intl",
                                              "typeorm", "prisma", "sequelize", "mongoose",
                                              "passport", "jwt", "class-validator"])},
    }


def find_dirs(root: Path, patterns: List[str]) -> List[Path]:
    """Find directories matching common patterns."""
    found = []
    for pattern in patterns:
        candidate = root / pattern
        if candidate.is_dir():
            found.append(candidate)
    return found


def walk_files(root: Path, extensions: Set[str] = CODE_EXTENSIONS) -> List[Path]:
    """Walk project tree, skip ignored dirs, return files matching extensions."""
    results = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in IGNORED_DIRS]
        for fname in filenames:
            if Path(fname).suffix in extensions:
                results.append(Path(dirpath) / fname)
    return results


def extract_routes_from_file(filepath: Path) -> List[Dict[str, str]]:
    """Extract route definitions from a file."""
    routes = []
    try:
        content = filepath.read_text(errors="replace")
    except IOError:
        return routes

    for pattern in ROUTE_PATTERNS:
        for match in re.finditer(pattern, content):
            path = match.group(1)
            if path and not path.startswith("http") and len(path) < 200:
                routes.append({
                    "path": path,
                    "source": str(filepath),
                    "line": content[:match.start()].count("\n") + 1,
                })
    return routes


def extract_routes_from_filesystem(pages_dir: Path, root: Path) -> List[Dict[str, str]]:
    """Infer routes from file-system routing (Next.js, Nuxt, SvelteKit)."""
    routes = []
    for filepath in sorted(pages_dir.rglob("*")):
        if filepath.is_file() and filepath.suffix in CODE_EXTENSIONS:
            rel = filepath.relative_to(pages_dir)
            route = "/" + str(rel.with_suffix("")).replace("\\", "/")
            # Normalize index routes
            route = re.sub(r"/index$", "", route) or "/"
            # Convert [param] to :param
            route = re.sub(r"\[\.\.\.(\w+)\]", r"*\1", route)
            route = re.sub(r"\[(\w+)\]", r":\1", route)
            routes.append({
                "path": route,
                "source": str(filepath),
                "filesystem": True,
            })
    return routes


def extract_apis_from_file(filepath: Path) -> List[Dict[str, Any]]:
    """Extract API calls from a file."""
    apis = []
    try:
        content = filepath.read_text(errors="replace")
    except IOError:
        return apis

    is_mock = any(re.search(p, content) for p in MOCK_SIGNALS)
    is_real = any(re.search(p, content) for p in REAL_API_SIGNALS)

    for pattern in API_PATH_PATTERNS:
        for match in re.finditer(pattern, content):
            path = match.group(1) if match.lastindex else match.group(0)
            if path and len(path) < 200:
                # Try to detect HTTP method
                context = content[max(0, match.start() - 100):match.end()]
                method = "UNKNOWN"
                for m in ["GET", "POST", "PUT", "DELETE", "PATCH"]:
                    if m.lower() in context.lower():
                        method = m
                        break

                apis.append({
                    "path": path,
                    "method": method,
                    "source": str(filepath),
                    "line": content[:match.start()].count("\n") + 1,
                    "integrated": is_real and not is_mock,
                    "mock_detected": is_mock,
                })
    return apis


def extract_enums(filepath: Path) -> List[Dict[str, Any]]:
    """Extract enum/constant definitions."""
    enums = []
    try:
        content = filepath.read_text(errors="replace")
    except IOError:
        return enums

    # TypeScript enums
    for match in re.finditer(r"enum\s+(\w+)\s*\{([^}]+)\}", content):
        name = match.group(1)
        body = match.group(2)
        values = re.findall(r"(\w+)\s*=\s*['\"]?([^,'\"\n]+)", body)
        enums.append({
            "name": name,
            "type": "enum",
            "values": {k.strip(): v.strip().rstrip(",") for k, v in values},
            "source": str(filepath),
        })

    # Object constant maps (const STATUS_MAP = { ... })
    for match in re.finditer(
        r"(?:const|export\s+const)\s+(\w*(?:MAP|STATUS|TYPE|ENUM|OPTION|ROLE|STATE)\w*)\s*[:=]\s*\{([^}]+)\}",
        content, re.IGNORECASE
    ):
        name = match.group(1)
        body = match.group(2)
        values = re.findall(r"['\"]?(\w+)['\"]?\s*:\s*['\"]([^'\"]+)['\"]", body)
        if values:
            enums.append({
                "name": name,
                "type": "constant_map",
                "values": dict(values),
                "source": str(filepath),
            })

    return enums


def extract_backend_routes(filepath: Path, framework: str) -> List[Dict[str, str]]:
    """Extract route definitions from NestJS controllers or Django url configs."""
    routes = []
    try:
        content = filepath.read_text(errors="replace")
    except IOError:
        return routes

    patterns = []
    if framework in ("nestjs", "express", "fastify"):
        patterns = NEST_ROUTE_PATTERNS
    elif framework == "django":
        patterns = DJANGO_ROUTE_PATTERNS

    # For NestJS, also grab the controller prefix
    controller_prefix = ""
    if framework == "nestjs":
        m = re.search(r"@Controller\s*\(\s*['\"]([^'\"]*)['\"]", content)
        if m:
            controller_prefix = "/" + m.group(1).strip("/")

    for pattern in patterns:
        for match in re.finditer(pattern, content):
            path = match.group(1)
            if not path or path.startswith("http") or len(path) > 200:
                continue
            # For NestJS method decorators, prepend controller prefix
            if framework == "nestjs" and not path.startswith("/"):
                full_path = f"{controller_prefix}/{path}".replace("//", "/")
            else:
                full_path = path if path.startswith("/") else f"/{path}"

            # Detect HTTP method from decorator name
            method = "UNKNOWN"
            ctx = content[max(0, match.start() - 30):match.start()]
            for m_name in ["Get", "Post", "Put", "Delete", "Patch"]:
                if f"@{m_name}" in ctx or f"@{m_name.lower()}" in ctx:
                    method = m_name.upper()
                    break

            routes.append({
                "path": full_path,
                "method": method,
                "source": str(filepath),
                "line": content[:match.start()].count("\n") + 1,
                "type": "backend",
            })
    return routes


def extract_models(filepath: Path, framework: str) -> List[Dict[str, Any]]:
    """Extract model/entity definitions from backend code."""
    models = []
    try:
        content = filepath.read_text(errors="replace")
    except IOError:
        return models

    patterns = PYTHON_MODEL_PATTERNS if framework in ("django", "fastapi", "flask") else NEST_MODEL_PATTERNS
    for pattern in patterns:
        for match in re.finditer(pattern, content):
            name = match.group(1)
            # Try to extract fields
            fields = []
            # For Django models: field_name = models.FieldType(...)
            if framework == "django":
                block_start = match.end()
                block = content[block_start:block_start + 2000]
                for fm in re.finditer(
                    r"(\w+)\s*=\s*models\.(\w+)\s*\(([^)]*)\)", block
                ):
                    fields.append({
                        "name": fm.group(1),
                        "type": fm.group(2),
                        "args": fm.group(3).strip()[:100],
                    })
            models.append({
                "name": name,
                "source": str(filepath),
                "framework": framework,
                "fields": fields,
            })
    return models


def count_components(files: List[Path]) -> Dict[str, int]:
    """Count components by type."""
    counts: Dict[str, int] = defaultdict(int)
    for f in files:
        if f.suffix in COMPONENT_EXTENSIONS:
            counts["components"] += 1
        elif f.suffix in {".ts", ".js"}:
            counts["modules"] += 1
    return dict(counts)


def analyze_project(project_root: Path) -> Dict[str, Any]:
    """Run full analysis on a frontend project."""
    root = Path(project_root).resolve()
    if not root.is_dir():
        return {"error": f"Not a directory: {root}"}

    # 1. Framework detection
    framework_info = detect_framework(root)

    # 2. File inventory
    all_files = walk_files(root)
    component_counts = count_components(all_files)

    # 3. Directory structure
    route_dirs = find_dirs(root, ROUTE_DIR_PATTERNS)
    api_dirs = find_dirs(root, API_DIR_PATTERNS)
    state_dirs = find_dirs(root, STATE_DIR_PATTERNS)
    i18n_dirs = find_dirs(root, I18N_DIR_PATTERNS)

    # 4. Routes (frontend + backend)
    routes = []
    fw = framework_info["framework"]

    # Frontend: config-based routes
    for f in all_files:
        if any(p in f.name.lower() for p in ["router", "routes", "routing"]):
            routes.extend(extract_routes_from_file(f))

    # Frontend: file-system routes (Next.js, Nuxt, SvelteKit)
    if fw in ("next", "nuxt", "sveltekit", "remix", "astro"):
        for d in route_dirs:
            routes.extend(extract_routes_from_filesystem(d, root))

    # Backend: NestJS controllers, Django urls
    if fw in ("nestjs", "express", "fastify", "django"):
        for f in all_files:
            if fw == "django" and "urls.py" in f.name:
                routes.extend(extract_backend_routes(f, fw))
            elif fw in ("nestjs", "express", "fastify") and ".controller." in f.name:
                routes.extend(extract_backend_routes(f, fw))

    # Deduplicate routes by path (+ method for backend)
    seen_paths: Set[str] = set()
    unique_routes = []
    for r in routes:
        key = r["path"] if r.get("type") != "backend" else f"{r.get('method', '')}:{r['path']}"
        if key not in seen_paths:
            seen_paths.add(key)
            unique_routes.append(r)
    routes = sorted(unique_routes, key=lambda r: r["path"])

    # 5. API calls
    apis = []
    for f in all_files:
        apis.extend(extract_apis_from_file(f))

    # Deduplicate APIs by path+method
    seen_apis: Set[Tuple[str, str]] = set()
    unique_apis = []
    for a in apis:
        key = (a["path"], a["method"])
        if key not in seen_apis:
            seen_apis.add(key)
            unique_apis.append(a)
    apis = sorted(unique_apis, key=lambda a: a["path"])

    # 6. Enums
    enums = []
    for f in all_files:
        enums.extend(extract_enums(f))

    # 7. Models/entities (backend)
    models = []
    if fw in ("django", "fastapi", "flask", "nestjs"):
        for f in all_files:
            if fw == "django" and "models.py" in f.name:
                models.extend(extract_models(f, fw))
            elif fw == "nestjs" and (".entity." in f.name or ".dto." in f.name):
                models.extend(extract_models(f, fw))

    # Deduplicate models by name
    seen_models: Set[str] = set()
    unique_models = []
    for m in models:
        if m["name"] not in seen_models:
            seen_models.add(m["name"])
            unique_models.append(m)
    models = sorted(unique_models, key=lambda m: m["name"])

    # Backend-specific directories
    controller_dirs = find_dirs(root, CONTROLLER_DIR_PATTERNS)
    model_dirs = find_dirs(root, MODEL_DIR_PATTERNS)
    dto_dirs = find_dirs(root, DTO_DIR_PATTERNS)

    # 8. Summary
    mock_count = sum(1 for a in apis if a.get("mock_detected"))
    real_count = sum(1 for a in apis if a.get("integrated"))
    backend_routes = [r for r in routes if r.get("type") == "backend"]
    frontend_routes = [r for r in routes if r.get("type") != "backend"]

    analysis = {
        "project": {
            "root": str(root),
            "name": framework_info.get("name", root.name),
            "framework": framework_info["framework"],
            "detected_frameworks": framework_info.get("detected_frameworks", []),
            "key_dependencies": framework_info.get("key_deps", {}),
            "stack_type": "backend" if fw in ("django", "fastapi", "flask", "nestjs", "express", "fastify") and not frontend_routes else
                          "fullstack" if backend_routes and frontend_routes else "frontend",
        },
        "structure": {
            "total_files": len(all_files),
            "components": component_counts,
            "route_dirs": [str(d) for d in route_dirs],
            "api_dirs": [str(d) for d in api_dirs],
            "state_dirs": [str(d) for d in state_dirs],
            "i18n_dirs": [str(d) for d in i18n_dirs],
            "controller_dirs": [str(d) for d in controller_dirs],
            "model_dirs": [str(d) for d in model_dirs],
            "dto_dirs": [str(d) for d in dto_dirs],
        },
        "routes": {
            "count": len(routes),
            "frontend_pages": frontend_routes,
            "backend_endpoints": backend_routes,
            "pages": routes,  # backward compat
        },
        "apis": {
            "total": len(apis),
            "integrated": real_count,
            "mock": mock_count,
            "endpoints": apis,
        },
        "enums": {
            "count": len(enums),
            "definitions": enums,
        },
        "models": {
            "count": len(models),
            "definitions": models,
        },
        "summary": {
            "pages": len(frontend_routes),
            "backend_endpoints": len(backend_routes),
            "api_endpoints": len(apis),
            "api_integrated": real_count,
            "api_mock": mock_count,
            "enums": len(enums),
            "models": len(models),
            "has_i18n": len(i18n_dirs) > 0,
            "has_state_management": len(state_dirs) > 0,
            "stack_type": "backend" if fw in ("django", "fastapi", "flask", "nestjs", "express", "fastify") and not frontend_routes else
                          "fullstack" if backend_routes and frontend_routes else "frontend",
        },
    }

    return analysis


def format_markdown(analysis: Dict[str, Any]) -> str:
    """Format analysis as markdown summary."""
    lines = []
    proj = analysis["project"]
    summary = analysis["summary"]
    stack = summary.get("stack_type", "frontend")

    lines.append(f"# Codebase Analysis: {proj['name'] or 'Project'}")
    lines.append("")
    lines.append(f"**Framework:** {proj['framework']}")
    lines.append(f"**Stack type:** {stack}")
    lines.append(f"**Total files:** {analysis['structure']['total_files']}")
    if summary.get("pages"):
        lines.append(f"**Frontend pages:** {summary['pages']}")
    if summary.get("backend_endpoints"):
        lines.append(f"**Backend endpoints:** {summary['backend_endpoints']}")
    lines.append(f"**API calls detected:** {summary['api_endpoints']} "
                 f"({summary['api_integrated']} integrated, {summary['api_mock']} mock)")
    lines.append(f"**Enums:** {summary['enums']}")
    if summary.get("models"):
        lines.append(f"**Models/entities:** {summary['models']}")
    lines.append(f"**i18n:** {'Yes' if summary['has_i18n'] else 'No'}")
    lines.append(f"**State management:** {'Yes' if summary['has_state_management'] else 'No'}")
    lines.append("")

    if analysis["routes"]["pages"]:
        lines.append("## Pages / Routes")
        lines.append("")
        lines.append("| # | Route | Source |")
        lines.append("|---|-------|--------|")
        for i, r in enumerate(analysis["routes"]["pages"], 1):
            src = r.get("source", "").split("/")[-1]
            fs = " (fs)" if r.get("filesystem") else ""
            lines.append(f"| {i} | `{r['path']}` | {src}{fs} |")
        lines.append("")

    if analysis["apis"]["endpoints"]:
        lines.append("## API Endpoints")
        lines.append("")
        lines.append("| Method | Path | Integrated | Source |")
        lines.append("|--------|------|-----------|--------|")
        for a in analysis["apis"]["endpoints"]:
            src = a.get("source", "").split("/")[-1]
            status = "✅" if a.get("integrated") else "⚠️ Mock"
            lines.append(f"| {a['method']} | `{a['path']}` | {status} | {src} |")
        lines.append("")

    if analysis["enums"]["definitions"]:
        lines.append("## Enums & Constants")
        lines.append("")
        for e in analysis["enums"]["definitions"]:
            lines.append(f"### {e['name']} ({e['type']})")
            if e["values"]:
                lines.append("| Key | Value |")
                lines.append("|-----|-------|")
                for k, v in e["values"].items():
                    lines.append(f"| {k} | {v} |")
            lines.append("")

    if analysis.get("models", {}).get("definitions"):
        lines.append("## Models / Entities")
        lines.append("")
        for m in analysis["models"]["definitions"]:
            lines.append(f"### {m['name']} ({m.get('framework', '')})")
            if m.get("fields"):
                lines.append("| Field | Type | Args |")
                lines.append("|-------|------|------|")
                for fld in m["fields"]:
                    lines.append(f"| {fld['name']} | {fld['type']} | {fld.get('args', '')} |")
            lines.append("")

    if proj.get("key_dependencies"):
        lines.append("## Key Dependencies")
        lines.append("")
        for dep, ver in sorted(proj["key_dependencies"].items()):
            lines.append(f"- `{dep}`: {ver}")
        lines.append("")

    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser(
        description="Analyze any codebase (frontend, backend, fullstack) for PRD generation"
    )
    parser.add_argument("project", help="Path to project root")
    parser.add_argument("-o", "--output", help="Output file (default: stdout)")
    parser.add_argument(
        "-f", "--format",
        choices=["json", "markdown"],
        default="json",
        help="Output format (default: json)",
    )
    args = parser.parse_args()

    analysis = analyze_project(Path(args.project))

    if args.format == "markdown":
        output = format_markdown(analysis)
    else:
        output = json.dumps(analysis, indent=2, ensure_ascii=False)

    if args.output:
        Path(args.output).write_text(output)
        print(f"Written to {args.output}")
    else:
        print(output)


if __name__ == "__main__":
    main()
