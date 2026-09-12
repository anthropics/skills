#!/usr/bin/env python3
"""Generate test cases (evals) by analyzing a skill directory.

Reads a skill's SKILL.md and bundled resources, then calls `claude -p`
to generate both quality evals (evals.json) and trigger evals for
description optimization.
"""

import argparse
import json
import os
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

from scripts.utils import parse_skill_md

# File extensions that are definitely binary — skip content preview
_BINARY_EXTENSIONS = frozenset({
    ".png", ".jpg", ".jpeg", ".gif", ".bmp", ".ico", ".webp", ".svg",
    ".pdf", ".doc", ".docx", ".xls", ".xlsx", ".pptx",
    ".zip", ".gz", ".tar", ".tgz", ".bz2", ".7z", ".rar", ".skill",
    ".woff", ".woff2", ".ttf", ".otf", ".eot",
    ".mp3", ".mp4", ".wav", ".avi", ".mov", ".mkv",
    ".pyc", ".pyo", ".so", ".dylib", ".dll", ".exe",
    ".sqlite", ".db",
})

# Cap on total skill context sent to Claude (chars). Beyond this,
# reference/script previews are truncated to keep the prompt manageable.
_MAX_CONTEXT_CHARS = 80_000
_MAX_FILE_PREVIEW_CHARS = 3000


def _call_claude(prompt: str, model: str | None, timeout: int = 300) -> str:
    """Run `claude -p` with the prompt on stdin and return the text response."""
    cmd = ["claude", "-p", "--output-format", "text"]
    if model:
        cmd.extend(["--model", model])

    env = {k: v for k, v in os.environ.items() if k != "CLAUDECODE"}

    result = subprocess.run(
        cmd,
        input=prompt,
        capture_output=True,
        text=True,
        env=env,
        timeout=timeout,
    )
    if result.returncode != 0:
        raise RuntimeError(
            f"claude -p exited {result.returncode}\nstderr: {result.stderr}"
        )
    return result.stdout


def _is_binary(path: Path) -> bool:
    """Check if a file is likely binary based on extension or content sniff."""
    if path.suffix.lower() in _BINARY_EXTENSIONS:
        return True
    # Sniff first 512 bytes for null bytes
    try:
        chunk = path.read_bytes()[:512]
        return b"\x00" in chunk
    except Exception:
        return True


def _scan_skill_directory(skill_path: Path) -> dict:
    """Scan a skill directory and collect metadata about its contents."""
    info: dict = {
        "scripts": [],
        "references": [],
        "assets": [],
        "other_files": [],
    }

    for child in sorted(skill_path.rglob("*")):
        if not child.is_file():
            continue
        rel = child.relative_to(skill_path)
        if rel.name == "SKILL.md":
            continue
        # Skip evals directory — those are outputs of this script
        if rel.parts and rel.parts[0] == "evals":
            continue

        parts = rel.parts
        category = parts[0] if len(parts) > 1 else None

        entry: dict = {"path": str(rel), "size": child.stat().st_size}

        if category in ("scripts", "references"):
            if _is_binary(child):
                entry["preview"] = f"(binary file, {child.suffix})"
            else:
                try:
                    content = child.read_text(errors="replace")[:_MAX_FILE_PREVIEW_CHARS]
                    entry["preview"] = content
                except Exception:
                    entry["preview"] = "(unreadable)"
            info[category].append(entry)
        elif category == "assets":
            info["assets"].append(entry)
        else:
            info["other_files"].append(entry)

    return info


def _build_skill_context(skill_path: Path) -> str:
    """Build a comprehensive context string from the skill directory.

    Enforces a total size cap so the prompt stays within Claude's limits.
    Prioritises SKILL.md content, then scripts, then references, then assets.
    """
    name, description, content = parse_skill_md(skill_path)
    dir_info = _scan_skill_directory(skill_path)

    ctx = f"# Skill: {name}\n\n"
    ctx += f"## Description\n{description}\n\n"
    ctx += f"## SKILL.md Full Content\n```\n{content}\n```\n\n"

    remaining = _MAX_CONTEXT_CHARS - len(ctx)

    def _append_section(header: str, items: list[dict], show_preview: bool) -> str:
        nonlocal remaining
        if not items or remaining <= 0:
            return ""
        section = f"{header}\n"
        for idx, item in enumerate(items):
            if remaining <= 200:
                section += f"- ... and {len(items) - idx} more files (truncated)\n"
                break
            if show_preview and "preview" in item:
                chunk = f"\n### {item['path']} ({item['size']} bytes)\n```\n{item['preview']}\n```\n"
            else:
                chunk = f"- {item['path']} ({item['size']} bytes)\n"
            if len(chunk) > remaining:
                section += f"- {item['path']} ({item['size']} bytes) (content omitted, too large)\n"
                remaining -= 80
            else:
                section += chunk
                remaining -= len(chunk)
        return section

    ctx += _append_section("## Bundled Scripts", dir_info["scripts"], show_preview=True)
    ctx += _append_section("\n## Reference Files", dir_info["references"], show_preview=True)
    ctx += _append_section("\n## Assets", dir_info["assets"], show_preview=False)

    return ctx


def _extract_balanced(response: str, open_ch: str, close_ch: str) -> str:
    """Extract a balanced JSON substring from response using brace/bracket matching.

    Tries code-fenced JSON first, then falls back to a balanced-delimiter parser.
    """
    open_esc = re.escape(open_ch)
    close_esc = re.escape(close_ch)
    fence_pattern = r"```(?:json)?\s*(" + open_esc + r"[\s\S]*?" + close_esc + r")\s*```"
    fence_match = re.search(fence_pattern, response)
    if fence_match:
        try:
            json.loads(fence_match.group(1))
            return fence_match.group(1)
        except json.JSONDecodeError:
            pass

    start = response.find(open_ch)
    if start == -1:
        raise ValueError(f"No JSON ({open_ch}...{close_ch}) found in response:\n{response[:500]}")

    depth = 0
    in_string = False
    escape = False
    for i in range(start, len(response)):
        c = response[i]
        if escape:
            escape = False
            continue
        if c == "\\":
            escape = True
            continue
        if c == '"':
            in_string = not in_string
            continue
        if in_string:
            continue
        if c == open_ch:
            depth += 1
        elif c == close_ch:
            depth -= 1
            if depth == 0:
                candidate = response[start : i + 1]
                try:
                    json.loads(candidate)
                    return candidate
                except json.JSONDecodeError:
                    break

    raise ValueError(
        f"Failed to extract valid JSON ({open_ch}...{close_ch}) from response:\n{response[:500]}"
    )


def _extract_json_object(response: str) -> dict:
    """Extract a JSON object from a Claude response."""
    return json.loads(_extract_balanced(response, "{", "}"))


def _extract_json_array(response: str) -> list:
    """Extract a JSON array from a Claude response."""
    return json.loads(_extract_balanced(response, "[", "]"))


def _validate_quality_evals(data: Any, skill_name: str) -> list[str]:
    """Validate quality evals structure and return a list of warnings."""
    warnings: list[str] = []

    if not isinstance(data, dict):
        return ["Root is not a JSON object"]
    if "evals" not in data:
        return ["Missing 'evals' key"]
    if not isinstance(data["evals"], list):
        return ["'evals' is not an array"]

    # Fix skill_name if Claude got it wrong
    if data.get("skill_name") != skill_name:
        warnings.append(f"Fixed skill_name: '{data.get('skill_name')}' -> '{skill_name}'")
        data["skill_name"] = skill_name

    seen_ids: set[int] = set()
    for i, ev in enumerate(data["evals"]):
        prefix = f"evals[{i}]"
        if not isinstance(ev, dict):
            warnings.append(f"{prefix}: not an object, skipped")
            continue

        # Ensure required fields exist
        if "id" not in ev:
            ev["id"] = i + 1
            warnings.append(f"{prefix}: missing 'id', auto-assigned {ev['id']}")
        if ev["id"] in seen_ids:
            ev["id"] = max(seen_ids) + 1 if seen_ids else 1
            warnings.append(f"{prefix}: duplicate id, reassigned to {ev['id']}")
        seen_ids.add(ev["id"])

        if "prompt" not in ev or not isinstance(ev.get("prompt"), str):
            warnings.append(f"{prefix}: missing or invalid 'prompt'")
        if "expected_output" not in ev:
            ev["expected_output"] = ""
            warnings.append(f"{prefix}: missing 'expected_output', set to empty")
        if "files" not in ev:
            ev["files"] = []
        if "expectations" not in ev:
            ev["expectations"] = []
            warnings.append(f"{prefix}: missing 'expectations', set to empty")

    return warnings


def _validate_trigger_evals(data: Any) -> list[str]:
    """Validate trigger evals structure and return a list of warnings."""
    warnings: list[str] = []

    if not isinstance(data, list):
        return ["Root is not a JSON array"]

    for i, item in enumerate(data):
        prefix = f"[{i}]"
        if not isinstance(item, dict):
            warnings.append(f"{prefix}: not an object")
            continue
        if "query" not in item or not isinstance(item.get("query"), str):
            warnings.append(f"{prefix}: missing or invalid 'query'")
        if "should_trigger" not in item:
            warnings.append(f"{prefix}: missing 'should_trigger', defaulting to true")
            item["should_trigger"] = True
        elif not isinstance(item["should_trigger"], bool):
            item["should_trigger"] = bool(item["should_trigger"])

    should = sum(1 for e in data if e.get("should_trigger"))
    should_not = len(data) - should
    if should == 0:
        warnings.append("No should-trigger queries — trigger optimization won't work")
    if should_not == 0:
        warnings.append("No should-NOT-trigger queries — false-positive detection won't work")

    return warnings


_DIAGNOSE_CHECKLIST = """\
- **Structure**: Is SKILL.md over 500 lines? Should content be split into references/?
- **Description**: Is it too vague to trigger reliably? Too narrow and missing common phrasings? Over 1024 chars?
- **Broken references**: Does SKILL.md mention files (scripts/, references/, assets/) that don't exist, or vice versa — files exist but are never referenced?
- **Instruction clarity**: Are there ambiguous steps, missing "why" explanations, or excessive MUST/NEVER/ALWAYS without reasoning?
- **Missing examples**: Would input/output examples make the instructions clearer?
- **Progressive disclosure**: Is too much detail crammed into SKILL.md when it could live in references/?
- **Scripts**: Are bundled scripts mentioned with clear guidance on when to use them?"""


def _require_skill_md(skill_path: Path) -> None:
    """Raise if the directory does not contain a SKILL.md."""
    if not (skill_path / "SKILL.md").exists():
        raise FileNotFoundError(
            f"No SKILL.md found at {skill_path}. "
            "Make sure you're pointing to the correct skill root directory."
        )


def diagnose_skill(
    skill_path: Path,
    model: str | None = None,
) -> list[dict]:
    """Diagnose a skill for common issues without generating test cases."""
    _require_skill_md(skill_path)
    skill_context = _build_skill_context(skill_path)

    prompt = f"""You are an expert at reviewing Claude Code skills. A "skill" extends Claude's capabilities with specialized workflows, scripts, and domain knowledge.

Analyze the following skill and report any issues you find:

{skill_context}

Check for:

{_DIAGNOSE_CHECKLIST}

Only report genuine issues. If the skill looks solid on a given dimension, don't mention it.

Respond with ONLY a JSON object in this exact format, no other text:

```json
{{
  "diagnostics": [
    {{
      "severity": "error | warning | suggestion",
      "issue": "Clear description of the problem",
      "location": "Where in the skill (e.g. 'SKILL.md line ~30', 'description', 'scripts/foo.py')",
      "fix": "Concrete suggestion for how to fix it"
    }}
  ]
}}
```

Severity levels:
- **error**: Will likely cause the skill to fail or behave incorrectly (broken file references, invalid frontmatter)
- **warning**: May degrade quality or triggering accuracy (vague description, SKILL.md too long, missing examples)
- **suggestion**: Nice-to-have improvement (better progressive disclosure, reusable scripts)

If the skill has no issues, return {{"diagnostics": []}}."""

    response = _call_claude(prompt, model, timeout=300)
    result = _extract_json_object(response)
    return result.get("diagnostics", [])


def generate_quality_evals(
    skill_path: Path,
    count: int = 3,
    model: str | None = None,
    existing_evals: dict | None = None,
) -> dict:
    """Generate quality evaluation test cases (evals.json format)."""
    _require_skill_md(skill_path)
    skill_context = _build_skill_context(skill_path)
    name, _, _ = parse_skill_md(skill_path)

    existing_context = ""
    if existing_evals and existing_evals.get("evals"):
        existing_context = f"""
The skill already has these test cases. Generate NEW test cases that cover DIFFERENT
capabilities. Avoid duplicating the scenarios below:

```json
{json.dumps(existing_evals["evals"], indent=2, ensure_ascii=False)}
```
"""

    prompt = f"""You are an expert at writing test cases for Claude Code skills. A "skill" extends Claude's capabilities with specialized workflows, scripts, and domain knowledge.

I need you to analyze the following skill AND generate realistic quality evaluation test cases for it:

{skill_context}
{existing_context}

## Task 1: Diagnose the skill

Before writing test cases, analyze the skill for common issues. Check for:

{_DIAGNOSE_CHECKLIST}

Only report genuine issues. If the skill looks solid, return an empty diagnostics array.

## Task 2: Generate {count} test cases

Each test case should:

1. **Be realistic** — Write prompts that a real user would actually type. Include specific details like file names, column names, personal context, casual language, typos, abbreviations. NOT abstract descriptions like "Process a file".

2. **Cover different use cases** — Each test case should exercise a different capability or workflow of the skill. Try to cover: common cases, edge cases, and complex multi-step scenarios.

3. **Have verifiable expectations** — Write 2-4 expectations per test case that can be objectively checked. Good expectations test meaningful outcomes (file content, format correctness, data accuracy), not just surface compliance (file exists). If the skill produces subjective output (writing, design, art), focus expectations on structural requirements (format, length, required sections) rather than quality judgments.

4. **Include input files only if the skill works with files** — If the skill is conversational or produces output from scratch, leave `files` as an empty array. Only specify input files when the skill genuinely needs them.

Respond with ONLY a JSON object in this exact format, no other text:

```json
{{
  "skill_name": "{name}",
  "diagnostics": [
    {{
      "severity": "error | warning | suggestion",
      "issue": "Clear description of the problem",
      "location": "Where in the skill (e.g. 'SKILL.md line ~30', 'description', 'scripts/foo.py')",
      "fix": "Concrete suggestion for how to fix it"
    }}
  ],
  "evals": [
    {{
      "id": 1,
      "prompt": "A realistic user prompt with specific details",
      "expected_output": "Human-readable description of what success looks like",
      "files": [],
      "expectations": [
        "Specific verifiable assertion 1",
        "Specific verifiable assertion 2"
      ]
    }}
  ],
  "input_files_to_create": [
    {{
      "path": "evals/files/example.csv",
      "description": "What this file should contain and its format"
    }}
  ]
}}
```

Severity levels:
- **error**: Will likely cause the skill to fail or behave incorrectly (broken file references, invalid frontmatter)
- **warning**: May degrade quality or triggering accuracy (vague description, SKILL.md too long, missing examples)
- **suggestion**: Nice-to-have improvement (better progressive disclosure, reusable scripts)

The `input_files_to_create` section lists input files the tests need (omit if none are needed). These won't be auto-created but serve as a guide for the user to prepare them.

Generate exactly {count} test cases."""

    response = _call_claude(prompt, model, timeout=600)
    result = _extract_json_object(response)

    warnings = _validate_quality_evals(result, name)
    if warnings:
        for w in warnings:
            print(f"  [warn] {w}", file=sys.stderr)

    return result


def generate_trigger_evals(
    skill_path: Path,
    count: int = 20,
    model: str | None = None,
    existing_evals: list[dict] | None = None,
) -> list[dict]:
    """Generate trigger evaluation test cases for description optimization."""
    _require_skill_md(skill_path)
    skill_context = _build_skill_context(skill_path)

    half = count // 2

    existing_context = ""
    if existing_evals:
        existing_context = f"""
The skill already has these trigger eval queries. Generate NEW queries that cover
DIFFERENT edge cases. Avoid duplicating the scenarios below:

```json
{json.dumps(existing_evals, indent=2, ensure_ascii=False)}
```
"""

    prompt = f"""You are an expert at writing trigger evaluation queries for Claude Code skills. Skills appear in Claude's available_skills list with their name and description. Claude decides whether to invoke a skill based on the description.

I need you to generate trigger evaluation queries for this skill:

{skill_context}
{existing_context}
Generate {count} queries total: approximately {half} should-trigger and {half} should-not-trigger.

**Critical requirements for query realism:**

Each query must read like something a real person would type into Claude Code. Include:
- Specific file paths, column names, company names, URLs
- Personal context ("my boss wants...", "I'm working on...")
- Casual language, abbreviations, occasional typos
- Mix of different lengths (some brief, some detailed)
- Backstory or situational context

**BAD examples** (too abstract):
- "Format this data"
- "Extract text from PDF"
- "Create a chart"

**GOOD examples** (realistic):
- "ok so my boss just sent me this xlsx file (its in my downloads, called something like 'Q4 sales final FINAL v2.xlsx') and she wants me to add a column that shows the profit margin as a percentage"
- "can you help me debug this react component? the state isn't updating when I click the button in src/components/Counter.tsx"

**For should-trigger queries ({half}):**
- Different phrasings of the same intent (formal, casual, terse)
- Cases where the user doesn't explicitly name the skill but clearly needs it
- Uncommon but valid use cases
- Cases where this skill competes with others but should win

**For should-NOT-trigger queries ({half}):**
- Focus on NEAR-MISSES: queries sharing keywords/concepts but needing something different
- Adjacent domains where a naive keyword match would trigger but shouldn't
- Queries touching on what the skill does but in a context where another tool is more appropriate
- Do NOT include obviously irrelevant queries (like "write fibonacci" for a PDF skill)

Respond with ONLY a JSON array, no other text:

```json
[
  {{"query": "realistic user prompt here...", "should_trigger": true}},
  {{"query": "another realistic prompt...", "should_trigger": false}}
]
```

Generate exactly {count} queries."""

    response = _call_claude(prompt, model, timeout=600)
    result = _extract_json_array(response)

    warnings = _validate_trigger_evals(result)
    if warnings:
        for w in warnings:
            print(f"  [warn] {w}", file=sys.stderr)

    return result


def _print_diagnostics(diagnostics: list[dict]) -> None:
    """Print formatted diagnostics to stderr."""
    if not diagnostics:
        return
    print(f"\n{'='*60}", file=sys.stderr)
    print("SKILL DIAGNOSTICS", file=sys.stderr)
    print(f"{'='*60}", file=sys.stderr)
    severity_icon = {"error": "[ERROR]", "warning": "[WARN] ", "suggestion": "[HINT] "}
    for d in diagnostics:
        sev = d.get("severity", "suggestion")
        icon = severity_icon.get(sev, "[????] ")
        print(f"  {icon} {d.get('issue', '(no description)')}", file=sys.stderr)
        if d.get("location"):
            print(f"         at: {d['location']}", file=sys.stderr)
        if d.get("fix"):
            print(f"         fix: {d['fix']}", file=sys.stderr)
    print(f"{'='*60}", file=sys.stderr)

    errors = sum(1 for d in diagnostics if d.get("severity") == "error")
    warns = sum(1 for d in diagnostics if d.get("severity") == "warning")
    suggestions = len(diagnostics) - errors - warns
    print(f"\nFound {errors} error(s), {warns} warning(s), {suggestions} suggestion(s).", file=sys.stderr)


def main():
    parser = argparse.ArgumentParser(
        description="Generate test cases by analyzing a skill directory"
    )
    parser.add_argument(
        "skill_path",
        help="Path to the skill directory containing SKILL.md",
    )
    parser.add_argument(
        "--type",
        choices=["quality", "trigger", "both", "diagnose"],
        default="both",
        help="Type of evals to generate, or 'diagnose' to only run diagnostics (default: both)",
    )
    parser.add_argument(
        "--quality-count",
        type=int,
        default=3,
        help="Number of quality eval test cases (default: 3)",
    )
    parser.add_argument(
        "--trigger-count",
        type=int,
        default=20,
        help="Number of trigger eval queries (default: 20)",
    )
    parser.add_argument(
        "--model",
        default=None,
        help="Model to use for generation (default: user's configured model)",
    )
    parser.add_argument(
        "--output-dir",
        default=None,
        help="Directory to save output files (default: <skill_path>/evals/)",
    )
    parser.add_argument(
        "--no-overwrite",
        action="store_true",
        help="Abort if output files already exist instead of overwriting",
    )
    parser.add_argument(
        "--append",
        action="store_true",
        help="Merge with existing evals instead of replacing them",
    )
    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Print progress to stderr",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print results to stdout without saving files",
    )
    args = parser.parse_args()

    skill_path = Path(args.skill_path).resolve()
    if not (skill_path / "SKILL.md").exists():
        print(f"Error: No SKILL.md found at {skill_path}", file=sys.stderr)
        print(
            "This script operates on a single skill directory that contains a SKILL.md file.\n"
            "Make sure you're pointing to the correct skill root, not a parent or sub-directory.",
            file=sys.stderr,
        )
        sys.exit(1)

    explicit_output_dir = args.output_dir is not None
    output_dir = Path(args.output_dir) if args.output_dir else skill_path / "evals"
    skill_name, skill_description, _ = parse_skill_md(skill_path)

    if args.verbose:
        print(f"Skill: {skill_name}", file=sys.stderr)
        print(f"Description: {skill_description[:100]}...", file=sys.stderr)

    # Load existing evals for context / merge
    existing_quality: dict | None = None
    existing_trigger: list[dict] | None = None
    quality_path = output_dir / "evals.json"
    trigger_path = output_dir / "trigger_evals.json"

    if quality_path.exists():
        try:
            existing_quality = json.loads(quality_path.read_text())
        except (json.JSONDecodeError, OSError):
            pass
    if trigger_path.exists():
        try:
            existing_trigger = json.loads(trigger_path.read_text())
        except (json.JSONDecodeError, OSError):
            pass

    # Check overwrite guard
    if args.no_overwrite and not args.dry_run:
        blocked = []
        if args.type in ("quality", "both") and quality_path.exists():
            blocked.append(str(quality_path))
        if args.type in ("trigger", "both") and trigger_path.exists():
            blocked.append(str(trigger_path))
        if blocked:
            print(f"Error: --no-overwrite set but files already exist: {', '.join(blocked)}", file=sys.stderr)
            sys.exit(1)

    # Diagnose-only mode
    if args.type == "diagnose":
        if args.verbose:
            print("\nRunning diagnostics...", file=sys.stderr)

        diagnostics = diagnose_skill(skill_path, model=args.model)

        if diagnostics:
            _print_diagnostics(diagnostics)
        else:
            print("\nNo issues found. The skill looks good!", file=sys.stderr)

        if args.dry_run or not explicit_output_dir:
            # Diagnostics only write to file when --output-dir is explicitly set.
            # By default, print to stdout so we don't pollute the skill directory.
            print(json.dumps(diagnostics, indent=2, ensure_ascii=False))
        else:
            output_dir.mkdir(parents=True, exist_ok=True)
            diag_path = output_dir / "diagnostics.json"
            diag_path.write_text(json.dumps(diagnostics, indent=2, ensure_ascii=False))
            print(f"Diagnostics saved to: {diag_path}", file=sys.stderr)

        has_evals = (quality_path.exists() and existing_quality and existing_quality.get("evals"))
        if not has_evals:
            print(
                "\nNote: This skill has no test cases yet. "
                "To generate evals, run again with --type both (or quality/trigger):\n"
                f"  python -m scripts.generate_evals {args.skill_path} --type both --verbose",
                file=sys.stderr,
            )
        return

    # Generate quality evals
    if args.type in ("quality", "both"):
        if args.verbose:
            print(f"\nGenerating {args.quality_count} quality eval(s)...", file=sys.stderr)

        quality_evals = generate_quality_evals(
            skill_path,
            count=args.quality_count,
            model=args.model,
            existing_evals=existing_quality if (args.append or existing_quality) else None,
        )

        # Merge with existing if --append
        if args.append and existing_quality and existing_quality.get("evals"):
            max_id = max((e.get("id", 0) for e in existing_quality["evals"]), default=0)
            for ev in quality_evals.get("evals", []):
                max_id += 1
                ev["id"] = max_id
            quality_evals["evals"] = existing_quality["evals"] + quality_evals["evals"]
            # Merge input_files_to_create
            existing_files = existing_quality.get("input_files_to_create", [])
            new_files = quality_evals.get("input_files_to_create", [])
            seen_paths = {f["path"] for f in existing_files}
            for f in new_files:
                if f["path"] not in seen_paths:
                    existing_files.append(f)
            quality_evals["input_files_to_create"] = existing_files
            if args.verbose:
                print(f"Merged: {len(quality_evals['evals'])} total quality evals", file=sys.stderr)

        # Display diagnostics
        diagnostics = quality_evals.pop("diagnostics", [])
        _print_diagnostics(diagnostics)

        if args.dry_run:
            print("=== Quality Evals (evals.json) ===")
            print(json.dumps(quality_evals, indent=2, ensure_ascii=False))
            if diagnostics:
                print("\n=== Diagnostics ===")
                print(json.dumps(diagnostics, indent=2, ensure_ascii=False))
        else:
            output_dir.mkdir(parents=True, exist_ok=True)
            quality_path.write_text(json.dumps(quality_evals, indent=2, ensure_ascii=False))
            print(f"Quality evals saved to: {quality_path}", file=sys.stderr)

        if args.verbose:
            n = len(quality_evals.get("evals", []))
            print(f"Generated {n} quality eval(s)", file=sys.stderr)
            files_needed = quality_evals.get("input_files_to_create", [])
            if files_needed:
                print("Input files to prepare:", file=sys.stderr)
                for f in files_needed:
                    print(f"  - {f['path']}: {f['description']}", file=sys.stderr)

    # Generate trigger evals
    if args.type in ("trigger", "both"):
        if args.verbose:
            print(f"\nGenerating {args.trigger_count} trigger eval(s)...", file=sys.stderr)

        trigger_evals = generate_trigger_evals(
            skill_path,
            count=args.trigger_count,
            model=args.model,
            existing_evals=existing_trigger if (args.append or existing_trigger) else None,
        )

        # Merge with existing if --append
        if args.append and existing_trigger:
            existing_queries = {e["query"] for e in existing_trigger}
            new_unique = [e for e in trigger_evals if e["query"] not in existing_queries]
            trigger_evals = existing_trigger + new_unique
            if args.verbose:
                print(f"Merged: {len(trigger_evals)} total trigger evals", file=sys.stderr)

        if args.dry_run:
            print("\n=== Trigger Evals (trigger_evals.json) ===")
            print(json.dumps(trigger_evals, indent=2, ensure_ascii=False))
        else:
            output_dir.mkdir(parents=True, exist_ok=True)
            trigger_path.write_text(json.dumps(trigger_evals, indent=2, ensure_ascii=False))
            print(f"Trigger evals saved to: {trigger_path}", file=sys.stderr)

        if args.verbose:
            should = sum(1 for e in trigger_evals if e.get("should_trigger"))
            should_not = len(trigger_evals) - should
            print(f"Generated {len(trigger_evals)} trigger eval(s) "
                  f"({should} should-trigger, {should_not} should-not-trigger)", file=sys.stderr)


if __name__ == "__main__":
    main()
