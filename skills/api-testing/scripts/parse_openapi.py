#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Extract endpoint inventory from OpenAPI 2.0 (Swagger) or OpenAPI 3.x docs for API test case design.

Usage (when run from project root where this skill lives, path is relative to project root):
  python .cursor/skills/api-test-generator/scripts/parse_openapi.py path/to/openapi.json
  python .cursor/skills/api-test-generator/scripts/parse_openapi.py path/to/openapi.yaml --output inventory.txt
"""

import argparse
import json
import sys
from pathlib import Path


def load_spec(path):
    """Load OpenAPI/Swagger doc from disk: supports .json and .yaml/.yml, parsed by extension."""
    path = Path(path)
    if not path.exists():
        raise FileNotFoundError(path)
    text = path.read_text(encoding="utf-8")
    # YAML requires pyyaml
    if path.suffix.lower() in (".yaml", ".yml"):
        try:
            import yaml
            return yaml.safe_load(text)
        except ImportError:
            raise RuntimeError("YAML requires PyYAML: pip install pyyaml")
    return json.loads(text)


def is_openapi3(spec):
    """Check if doc is OpenAPI 3.x (openapi field starts with 3)."""
    return "openapi" in spec and str(spec.get("openapi", "")).startswith("3")


def is_swagger2(spec):
    """Check if doc is Swagger 2.0."""
    return "swagger" in spec and spec.get("swagger") == "2.0"


def get_paths(spec):
    """Get paths object from doc (compatible with different field names)."""
    return spec.get("paths") or spec.get("path") or {}


def get_servers(spec):
    """Only OpenAPI 3.x has servers; return first server url list."""
    if is_openapi3(spec):
        servers = spec.get("servers") or []
        return [s.get("url", "") for s in servers if isinstance(s, dict)]
    return []


def collect_endpoints(spec):
    """
    Walk paths and collect each path's HTTP method operations.
    Returns list of items with path, method, summary, parameters, requestBody, security, etc.
    """
    paths = get_paths(spec)
    endpoints = []
    for path, path_item in paths.items():
        if not isinstance(path_item, dict):
            continue
        # Standard HTTP methods
        for method in ("get", "post", "put", "patch", "delete", "head", "options"):
            op = path_item.get(method)
            if not isinstance(op, dict):
                continue
            operation_id = op.get("operationId") or op.get("operation_id") or ""
            summary = op.get("summary") or op.get("description") or ""
            tags = op.get("tags") or []
            security = op.get("security") or path_item.get("security") or []
            # Collect parameters (query/path/header etc.)
            params = []
            for p in op.get("parameters") or path_item.get("parameters") or []:
                if isinstance(p, dict):
                    params.append({
                        "in": p.get("in"),
                        "name": p.get("name"),
                        "required": p.get("required", False),
                    })
            # OpenAPI 3 uses requestBody, Swagger 2 uses parameters.in=body
            body = None
            if "requestBody" in op:
                body = "requestBody"
            elif any(p.get("in") == "body" for p in (op.get("parameters") or [])):
                body = "body"
            endpoints.append({
                "path": path,
                "method": method.upper(),
                "operationId": operation_id,
                "summary": summary,
                "tags": tags,
                "parameters": params,
                "requestBody": body,
                "security": security,
            })
    return endpoints


def format_inventory(spec, endpoints, base_url=""):
    """Format endpoint list as "method path - summary" text inventory with API title, version, and Base URL."""
    lines = []
    title = spec.get("info", {}).get("title") or "API"
    version = spec.get("info", {}).get("version") or ""
    lines.append("# {} (version {})".format(title, version))
    if base_url:
        lines.append("# Base URL: {}".format(base_url))
    lines.append("")
    for e in endpoints:
        line = "{:6} {}".format(e["method"], e["path"])
        if e["summary"]:
            line += "  - {}".format(e["summary"])
        lines.append(line)
    return "\n".join(lines)


def main():
    """CLI entry: parse args, load doc, extract endpoints, output to stdout or file."""
    parser = argparse.ArgumentParser(description="Extract endpoint inventory from OpenAPI/Swagger doc")
    parser.add_argument("spec_path", help="Path to openapi.json or openapi.yaml")
    parser.add_argument("--output", "-o", help="Write to file (default: stdout)")
    parser.add_argument("--base-url", help="Base URL to write in inventory header")
    args = parser.parse_args()

    try:
        spec = load_spec(args.spec_path)
    except Exception as e:
        print("Failed to load doc: {}".format(e), file=sys.stderr)
        sys.exit(1)

    if not is_openapi3(spec) and not is_swagger2(spec):
        print("Unsupported doc format; need openapi 3.x or swagger 2.0", file=sys.stderr)
        sys.exit(1)

    # Prefer CLI --base-url, else first OpenAPI 3 servers URL
    base_url = args.base_url or (get_servers(spec) and get_servers(spec)[0]) or ""
    endpoints = collect_endpoints(spec)
    out = format_inventory(spec, endpoints, base_url)

    if args.output:
        Path(args.output).write_text(out, encoding="utf-8")
        print("Wrote {} endpoints to {}".format(len(endpoints), args.output), file=sys.stderr)
    else:
        print(out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
