#!/usr/bin/env python3
"""Version and diff prompts with a local JSONL history store.

Commands:
- add
- list
- diff
- changelog

Input modes:
- prompt text via --prompt, --prompt-file, --input JSON, or stdin JSON
"""

import argparse
import difflib
import json
import sys
from dataclasses import dataclass, asdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, List, Optional


class CLIError(Exception):
    """Raised for expected CLI failures."""


@dataclass
class PromptVersion:
    name: str
    version: int
    author: str
    timestamp: str
    change_note: str
    prompt: str


def add_common_subparser_args(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--store", default=".prompt_versions.jsonl", help="JSONL history file path.")
    parser.add_argument("--input", help="Optional JSON input file with prompt payload.")
    parser.add_argument("--format", choices=["text", "json"], default="text", help="Output format.")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Version and diff prompts.")

    sub = parser.add_subparsers(dest="command", required=True)

    add = sub.add_parser("add", help="Add a new prompt version.")
    add_common_subparser_args(add)
    add.add_argument("--name", required=True, help="Prompt identifier.")
    add.add_argument("--prompt", help="Prompt text.")
    add.add_argument("--prompt-file", help="Prompt file path.")
    add.add_argument("--author", default="unknown", help="Author name.")
    add.add_argument("--change-note", default="", help="Reason for this revision.")

    ls = sub.add_parser("list", help="List versions for a prompt.")
    add_common_subparser_args(ls)
    ls.add_argument("--name", required=True, help="Prompt identifier.")

    diff = sub.add_parser("diff", help="Diff two prompt versions.")
    add_common_subparser_args(diff)
    diff.add_argument("--name", required=True, help="Prompt identifier.")
    diff.add_argument("--from-version", type=int, required=True)
    diff.add_argument("--to-version", type=int, required=True)

    changelog = sub.add_parser("changelog", help="Show changelog for a prompt.")
    add_common_subparser_args(changelog)
    changelog.add_argument("--name", required=True, help="Prompt identifier.")
    return parser


def read_optional_json(input_path: Optional[str]) -> Dict[str, Any]:
    if input_path:
        try:
            return json.loads(Path(input_path).read_text(encoding="utf-8"))
        except Exception as exc:
            raise CLIError(f"Failed reading --input: {exc}") from exc

    if not sys.stdin.isatty():
        raw = sys.stdin.read().strip()
        if raw:
            try:
                return json.loads(raw)
            except json.JSONDecodeError as exc:
                raise CLIError(f"Invalid JSON from stdin: {exc}") from exc

    return {}


def read_store(path: Path) -> List[PromptVersion]:
    if not path.exists():
        return []
    versions: List[PromptVersion] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        obj = json.loads(line)
        versions.append(PromptVersion(**obj))
    return versions


def write_store(path: Path, versions: List[PromptVersion]) -> None:
    payload = "\n".join(json.dumps(asdict(v), ensure_ascii=True) for v in versions)
    path.write_text(payload + ("\n" if payload else ""), encoding="utf-8")


def get_prompt_text(args: argparse.Namespace, payload: Dict[str, Any]) -> str:
    if args.prompt:
        return args.prompt
    if args.prompt_file:
        try:
            return Path(args.prompt_file).read_text(encoding="utf-8")
        except Exception as exc:
            raise CLIError(f"Failed reading prompt file: {exc}") from exc
    if payload.get("prompt"):
        return str(payload["prompt"])
    raise CLIError("Prompt content required via --prompt, --prompt-file, --input JSON, or stdin JSON.")


def next_version(versions: List[PromptVersion], name: str) -> int:
    existing = [v.version for v in versions if v.name == name]
    return (max(existing) + 1) if existing else 1


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    payload = read_optional_json(args.input)

    store_path = Path(args.store)
    versions = read_store(store_path)

    if args.command == "add":
        prompt_name = str(payload.get("name", args.name))
        prompt_text = get_prompt_text(args, payload)
        author = str(payload.get("author", args.author))
        change_note = str(payload.get("change_note", args.change_note))

        item = PromptVersion(
            name=prompt_name,
            version=next_version(versions, prompt_name),
            author=author,
            timestamp=datetime.now(timezone.utc).isoformat(),
            change_note=change_note,
            prompt=prompt_text,
        )
        versions.append(item)
        write_store(store_path, versions)
        output: Dict[str, Any] = {"added": asdict(item), "store": str(store_path.resolve())}

    elif args.command == "list":
        prompt_name = str(payload.get("name", args.name))
        matches = [asdict(v) for v in versions if v.name == prompt_name]
        output = {"name": prompt_name, "versions": matches}

    elif args.command == "changelog":
        prompt_name = str(payload.get("name", args.name))
        matches = [v for v in versions if v.name == prompt_name]
        entries = [
            {
                "version": v.version,
                "author": v.author,
                "timestamp": v.timestamp,
                "change_note": v.change_note,
            }
            for v in matches
        ]
        output = {"name": prompt_name, "changelog": entries}

    elif args.command == "diff":
        prompt_name = str(payload.get("name", args.name))
        from_v = int(payload.get("from_version", args.from_version))
        to_v = int(payload.get("to_version", args.to_version))

        by_name = [v for v in versions if v.name == prompt_name]
        old = next((v for v in by_name if v.version == from_v), None)
        new = next((v for v in by_name if v.version == to_v), None)
        if not old or not new:
            raise CLIError("Requested versions not found for prompt name.")

        diff_lines = list(
            difflib.unified_diff(
                old.prompt.splitlines(),
                new.prompt.splitlines(),
                fromfile=f"{prompt_name}@v{from_v}",
                tofile=f"{prompt_name}@v{to_v}",
                lineterm="",
            )
        )
        output = {
            "name": prompt_name,
            "from_version": from_v,
            "to_version": to_v,
            "diff": diff_lines,
        }

    else:
        raise CLIError("Unknown command.")

    if args.format == "json":
        print(json.dumps(output, indent=2))
    else:
        if args.command == "add":
            added = output["added"]
            print("Prompt version added")
            print(f"- name: {added['name']}")
            print(f"- version: {added['version']}")
            print(f"- author: {added['author']}")
            print(f"- store: {output['store']}")
        elif args.command in ("list", "changelog"):
            print(f"Prompt: {output['name']}")
            key = "versions" if args.command == "list" else "changelog"
            items = output[key]
            if not items:
                print("- no entries")
            else:
                for item in items:
                    line = f"- v{item.get('version')} by {item.get('author')} at {item.get('timestamp')}"
                    note = item.get("change_note")
                    if note:
                        line += f" | {note}"
                    print(line)
        else:
            print("\n".join(output["diff"]) if output["diff"] else "No differences.")

    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except CLIError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        raise SystemExit(2)
