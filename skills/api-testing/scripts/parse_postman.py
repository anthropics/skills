#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Extract endpoint inventory from Postman Collection 2.x JSON for API test case design.

Usage (when run from project root where this skill lives, path is relative to project root):
  python .cursor/skills/api-test-generator/scripts/parse_postman.py path/to/collection.json
  python .cursor/skills/api-test-generator/scripts/parse_postman.py path/to/collection.json --output inventory.txt
"""

import argparse
import json
import sys
from pathlib import Path


def load_collection(path):
    """Load Postman Collection JSON file from disk."""
    path = Path(path)
    if not path.exists():
        raise FileNotFoundError(path)
    return json.loads(path.read_text(encoding="utf-8"))


def is_v2(collection):
    """Determine if collection is Postman Collection 2.x format via info.schema etc."""
    info = collection.get("info") or {}
    schema = (info.get("schema") or "").lower()
    return "2." in schema or "v2" in schema or "postman" in str(collection.get("info", {}))


def walk_requests(item, base_path="", results=None):
    """
    Recursively walk Collection item tree: if a node has request, treat as one request and add to results,
    then recurse into child items; child nodes inherit current folder path.
    """
    if results is None:
        results = []
    name = item.get("name", "")
    # Leaf node: items with request are actual requests
    if "request" in item:
        req = item["request"]
        if isinstance(req, dict):
            method = (req.get("method") or "GET").upper()
            url = req.get("url")
            # url may be string or object (path/raw etc.)
            if isinstance(url, str):
                path = url
            elif isinstance(url, dict):
                path = url.get("path") or ""
                if isinstance(path, list):
                    path = "/" + "/".join(str(p) for p in path)
                raw = url.get("raw", "")
                if raw and path and not path.startswith("/"):
                    path = raw
            else:
                path = ""
            results.append({
                "method": method,
                "path": path,
                "name": name,
                "folder": base_path,
            })
    # Recurse into children (folders or nested requests)
    for child in item.get("item") or []:
        if isinstance(child, dict):
            folder = "{}/{}".format(base_path, name).strip("/") if name else base_path
            walk_requests(child, folder, results)
    return results


def collect_endpoints(collection):
    """Starting from Collection root item, recursively collect all requests into endpoint list."""
    results = []
    for item in collection.get("item") or []:
        if isinstance(item, dict):
            walk_requests(item, "", results)
    return results


def format_inventory(collection, endpoints, base_url=""):
    """Format endpoint list as "method path - name" text inventory with Collection name and Base URL."""
    info = collection.get("info") or {}
    name = info.get("name") or "Postman Collection"
    lines = ["# {}".format(name), ""]
    if base_url:
        lines.append("# Base URL: {}".format(base_url))
        lines.append("")
    for e in endpoints:
        path = e["path"]
        line = "{:6} {}".format(e["method"], path)
        if e.get("name"):
            line += "  - {}".format(e["name"])
        lines.append(line)
    return "\n".join(lines)


def main():
    """CLI entry: parse args, load Collection, extract endpoints, output to stdout or file."""
    parser = argparse.ArgumentParser(description="Extract endpoint inventory from Postman Collection")
    parser.add_argument("collection_path", help="Path to Postman-exported collection JSON")
    parser.add_argument("--output", "-o", help="Write to file (default: stdout)")
    parser.add_argument("--base-url", help="Base URL to write in inventory header")
    args = parser.parse_args()

    try:
        collection = load_collection(args.collection_path)
    except Exception as e:
        print("Failed to load Collection: {}".format(e), file=sys.stderr)
        sys.exit(1)

    if not is_v2(collection):
        print("Warning: may not be v2 format; continuing.", file=sys.stderr)

    base_url = args.base_url or ""
    endpoints = collect_endpoints(collection)
    out = format_inventory(collection, endpoints, base_url)

    if args.output:
        Path(args.output).write_text(out, encoding="utf-8")
        print("Wrote {} endpoints to {}".format(len(endpoints), args.output), file=sys.stderr)
    else:
        print(out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
