#!/usr/bin/env python3
"""Validate MCP tool manifest files for common contract issues.

Input sources:
- --input <manifest.json>
- stdin JSON

Validation domains:
- structural correctness
- naming hygiene
- schema consistency
- descriptive completeness
"""

import argparse
import json
import re
import sys
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple


TOOL_NAME_RE = re.compile(r"^[a-z0-9_]{3,64}$")


class CLIError(Exception):
    """Raised for expected CLI failures."""


@dataclass
class ValidationResult:
    errors: List[str]
    warnings: List[str]
    tool_count: int


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Validate MCP tool definitions.")
    parser.add_argument("--input", help="Path to manifest JSON file. If omitted, reads from stdin.")
    parser.add_argument("--strict", action="store_true", help="Exit non-zero when errors are found.")
    parser.add_argument("--format", choices=["text", "json"], default="text", help="Output format.")
    return parser.parse_args()


def load_manifest(input_path: Optional[str]) -> Dict[str, Any]:
    if input_path:
        try:
            data = Path(input_path).read_text(encoding="utf-8")
        except Exception as exc:
            raise CLIError(f"Failed reading --input: {exc}") from exc
    else:
        if sys.stdin.isatty():
            raise CLIError("No input provided. Use --input or pipe manifest JSON via stdin.")
        data = sys.stdin.read().strip()
        if not data:
            raise CLIError("Empty stdin.")

    try:
        payload = json.loads(data)
    except json.JSONDecodeError as exc:
        raise CLIError(f"Invalid JSON input: {exc}") from exc

    if not isinstance(payload, dict):
        raise CLIError("Manifest root must be a JSON object.")
    return payload


def validate_schema(tool_name: str, schema: Dict[str, Any]) -> Tuple[List[str], List[str]]:
    errors: List[str] = []
    warnings: List[str] = []

    if schema.get("type") != "object":
        errors.append(f"{tool_name}: inputSchema.type must be 'object'.")

    props = schema.get("properties", {})
    if not isinstance(props, dict):
        errors.append(f"{tool_name}: inputSchema.properties must be an object.")
        props = {}

    required = schema.get("required", [])
    if not isinstance(required, list):
        errors.append(f"{tool_name}: inputSchema.required must be an array.")
        required = []

    prop_keys = set(props.keys())
    for req in required:
        if req not in prop_keys:
            errors.append(f"{tool_name}: required field '{req}' is not defined in properties.")

    if not props:
        warnings.append(f"{tool_name}: no input properties declared.")

    for pname, pdef in props.items():
        if not isinstance(pdef, dict):
            errors.append(f"{tool_name}: property '{pname}' must be an object.")
            continue
        ptype = pdef.get("type")
        if not ptype:
            warnings.append(f"{tool_name}: property '{pname}' has no explicit type.")

    return errors, warnings


def validate_manifest(payload: Dict[str, Any]) -> ValidationResult:
    errors: List[str] = []
    warnings: List[str] = []

    tools = payload.get("tools")
    if not isinstance(tools, list):
        raise CLIError("Manifest must include a 'tools' array.")

    seen_names = set()
    for idx, tool in enumerate(tools):
        if not isinstance(tool, dict):
            errors.append(f"tool[{idx}] is not an object.")
            continue

        name = str(tool.get("name", "")).strip()
        desc = str(tool.get("description", "")).strip()
        schema = tool.get("inputSchema")

        if not name:
            errors.append(f"tool[{idx}] missing name.")
            continue

        if name in seen_names:
            errors.append(f"duplicate tool name: {name}")
        seen_names.add(name)

        if not TOOL_NAME_RE.match(name):
            warnings.append(
                f"{name}: non-standard naming; prefer lowercase snake_case (3-64 chars, [a-z0-9_])."
            )

        if len(desc) < 10:
            warnings.append(f"{name}: description too short; provide actionable purpose.")

        if not isinstance(schema, dict):
            errors.append(f"{name}: missing or invalid inputSchema object.")
            continue

        schema_errors, schema_warnings = validate_schema(name, schema)
        errors.extend(schema_errors)
        warnings.extend(schema_warnings)

    return ValidationResult(errors=errors, warnings=warnings, tool_count=len(tools))


def to_text(result: ValidationResult) -> str:
    lines = [
        "MCP manifest validation",
        f"- tools: {result.tool_count}",
        f"- errors: {len(result.errors)}",
        f"- warnings: {len(result.warnings)}",
    ]
    if result.errors:
        lines.append("Errors:")
        lines.extend([f"- {item}" for item in result.errors])
    if result.warnings:
        lines.append("Warnings:")
        lines.extend([f"- {item}" for item in result.warnings])
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    payload = load_manifest(args.input)
    result = validate_manifest(payload)

    if args.format == "json":
        print(json.dumps(asdict(result), indent=2))
    else:
        print(to_text(result))

    if args.strict and result.errors:
        return 1
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except CLIError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
