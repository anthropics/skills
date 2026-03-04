#!/usr/bin/env python3
"""
validate_file.py - Quick syntax and integrity validation after edits.

Validates files based on their type to catch common post-edit breakage:
- Python: AST parse check
- JavaScript/TypeScript: Node --check
- JSON: json.loads
- XML/HTML: basic tag balance
- YAML: yaml.safe_load
- General: encoding check, line ending consistency, trailing whitespace

Usage:
    python validate_file.py file.py
    python validate_file.py file.js
    python validate_file.py file.json
    python validate_file.py *.py              # Multiple files
    python validate_file.py --all src/        # All supported files in directory
"""

import argparse
import ast
import json
import os
import subprocess
import sys
from pathlib import Path


def validate_python(filepath):
    """Validate Python syntax via AST parsing."""
    try:
        with open(filepath, 'r') as f:
            source = f.read()
        ast.parse(source)
        return True, "Python syntax OK"
    except SyntaxError as e:
        return False, f"Python syntax error at line {e.lineno}: {e.msg}"
    except Exception as e:
        return False, f"Python validation error: {e}"


def validate_javascript(filepath):
    """Validate JavaScript/TypeScript syntax via Node."""
    try:
        result = subprocess.run(
            ["node", "--check", str(filepath)],
            capture_output=True, text=True, timeout=10
        )
        if result.returncode == 0:
            return True, "JavaScript syntax OK"
        else:
            error = result.stderr.strip().split('\n')[0] if result.stderr else "Unknown error"
            return False, f"JavaScript error: {error}"
    except FileNotFoundError:
        return None, "Node.js not available for JS validation"
    except subprocess.TimeoutExpired:
        return None, "JS validation timed out"


def validate_json(filepath):
    """Validate JSON syntax."""
    try:
        with open(filepath, 'r') as f:
            json.load(f)
        return True, "JSON syntax OK"
    except json.JSONDecodeError as e:
        return False, f"JSON error at line {e.lineno}, col {e.colno}: {e.msg}"


def validate_yaml(filepath):
    """Validate YAML syntax."""
    try:
        import yaml
        with open(filepath, 'r') as f:
            yaml.safe_load(f)
        return True, "YAML syntax OK"
    except ImportError:
        return None, "PyYAML not available"
    except yaml.YAMLError as e:
        return False, f"YAML error: {e}"


def validate_xml(filepath):
    """Validate XML/HTML basic tag balance."""
    try:
        from xml.etree import ElementTree
        ElementTree.parse(filepath)
        return True, "XML syntax OK"
    except ElementTree.ParseError as e:
        return False, f"XML error: {e}"


def validate_encoding(filepath):
    """Check file encoding and common issues."""
    issues = []
    
    try:
        with open(filepath, 'rb') as f:
            raw = f.read()
    except Exception as e:
        return False, f"Cannot read file: {e}"

    # Check for BOM
    if raw.startswith(b'\xef\xbb\xbf'):
        issues.append("Has UTF-8 BOM (may cause issues)")

    # Check for mixed line endings
    has_crlf = b'\r\n' in raw
    has_lf = b'\n' in raw.replace(b'\r\n', b'')
    has_cr = b'\r' in raw.replace(b'\r\n', b'')
    
    endings = []
    if has_crlf: endings.append("CRLF")
    if has_lf: endings.append("LF")
    if has_cr: endings.append("CR")
    
    if len(endings) > 1:
        issues.append(f"Mixed line endings: {', '.join(endings)}")

    # Check for null bytes (binary content in text file)
    if b'\x00' in raw:
        issues.append("Contains null bytes (possibly binary)")

    # Try UTF-8 decode
    try:
        raw.decode('utf-8')
    except UnicodeDecodeError as e:
        issues.append(f"Not valid UTF-8 at byte {e.start}")

    # Check for trailing whitespace (common after bad edits)
    try:
        text = raw.decode('utf-8', errors='replace')
        trailing_ws_lines = []
        for i, line in enumerate(text.split('\n'), 1):
            if line != line.rstrip() and line.strip():  # Has trailing WS and isn't blank
                trailing_ws_lines.append(i)
        if len(trailing_ws_lines) > 10:
            issues.append(f"Trailing whitespace on {len(trailing_ws_lines)} lines")
    except Exception:
        pass

    if issues:
        return None, "Encoding warnings: " + "; ".join(issues)
    return True, "Encoding OK (UTF-8, consistent line endings)"


def validate_file(filepath):
    """Validate a file based on its extension."""
    filepath = Path(filepath)
    ext = filepath.suffix.lower()
    results = []

    # Always check encoding
    ok, msg = validate_encoding(filepath)
    results.append((ok, msg))

    # Type-specific validation
    validators = {
        '.py': validate_python,
        '.js': validate_javascript,
        '.mjs': validate_javascript,
        '.ts': validate_javascript,
        '.json': validate_json,
        '.yaml': validate_yaml,
        '.yml': validate_yaml,
        '.xml': validate_xml,
        '.html': validate_xml,
        '.svg': validate_xml,
    }

    if ext in validators:
        ok, msg = validators[ext](filepath)
        results.append((ok, msg))

    return results


def main():
    parser = argparse.ArgumentParser(description="Validate file integrity after edits")
    parser.add_argument("files", nargs="+", help="Files or directories to validate")
    parser.add_argument("--all", action="store_true",
                        help="Recursively validate all supported files in directories")
    args = parser.parse_args()

    supported_exts = {'.py', '.js', '.mjs', '.ts', '.json', '.yaml', '.yml', 
                      '.xml', '.html', '.svg'}

    files_to_check = []
    for path_str in args.files:
        path = Path(path_str)
        if path.is_dir() and args.all:
            for ext in supported_exts:
                files_to_check.extend(path.rglob(f"*{ext}"))
        elif path.is_file():
            files_to_check.append(path)
        else:
            print(f"Warning: {path_str} not found, skipping")

    if not files_to_check:
        print("No files to validate")
        sys.exit(1)

    total_ok = 0
    total_warn = 0
    total_fail = 0

    for filepath in sorted(files_to_check):
        results = validate_file(filepath)
        
        has_fail = any(ok is False for ok, _ in results)
        has_warn = any(ok is None for ok, _ in results)
        
        if has_fail:
            status = "FAIL"
            total_fail += 1
        elif has_warn:
            status = "WARN"
            total_warn += 1
        else:
            status = " OK "
            total_ok += 1

        print(f"[{status}] {filepath}")
        for ok, msg in results:
            if ok is False:
                print(f"       ERROR: {msg}")
            elif ok is None:
                print(f"       WARN:  {msg}")

    print(f"\nResults: {total_ok} OK, {total_warn} warnings, {total_fail} failures")
    sys.exit(0 if total_fail == 0 else 1)


if __name__ == "__main__":
    main()
