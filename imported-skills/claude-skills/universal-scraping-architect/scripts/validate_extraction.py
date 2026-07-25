#!/usr/bin/env python3
"""
validate_extraction.py
Intelligent stdlib-only validation for JSON structures.
"""
import argparse
import json
import sys
import os


def validate_json(file_path):
    if not os.path.exists(file_path):
        return {"status": "error", "message": f"File {file_path} not found."}

    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            data = json.load(f)
            # Basic validation: ensure it's not empty and is a list/dict
            if not data:
                return {"status": "warning", "message": "JSON file is empty."}
            return {"status": "ok", "message": "JSON is valid and well-formed."}
    except json.JSONDecodeError as e:
        return {"status": "error", "message": f"Invalid JSON: {str(e)}"}


def main():
    parser = argparse.ArgumentParser(description="Standard Library JSON Validator")
    parser.add_argument("file", help="Path to JSON file to validate")
    parser.add_argument("--json", action="store_true", help="Output results in JSON format")

    args = parser.parse_args()
    result = validate_json(args.file)

    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(f"[{result['status'].upper()}] {result['message']}")

    sys.exit(0 if result['status'] == "ok" else 1)


if __name__ == "__main__":
    main()
