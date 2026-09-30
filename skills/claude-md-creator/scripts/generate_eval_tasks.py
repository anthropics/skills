#!/usr/bin/env python3
"""
Phase 3 helper: Generate eval task skeletons from verified claims.

Reads claims.json and coherence_report.json to produce a skeleton
eval_tasks.json. The eval_generator agent enriches this with natural
task prompts and additional checks, but this script handles the
mechanical grouping and check-type inference.

Usage:
    python -m scripts.generate_eval_tasks <claims.json> <coherence.json> <project-root> [--output <path>]
"""

import argparse
import json
import re
from pathlib import Path


# ---------------------------------------------------------------------------
# Claim grouping heuristics
# ---------------------------------------------------------------------------

# Claim types eligible for blind-test eval tasks
TESTABLE_TYPES = {
    "convention",
    "naming_pattern",
    "import_rule",
    "architecture",
    "path_reference",
}

# Maximum number of eval tasks to generate
MAX_TASKS = 7
MIN_TASKS = 3


def _section_key(claim: dict) -> str:
    """Normalize section name for grouping."""
    return claim.get("source_section", "Other").strip().lower()


def _infer_check_type(claim: dict) -> dict:
    """Infer the best check_type and parameters for a claim."""
    claim_type = claim["type"]
    extracted = claim.get("extracted", {})

    if claim_type == "path_reference":
        path = extracted.get("path", "")
        if extracted.get("is_directory"):
            return {
                "check_type": "file_location",
                "expected_dir": path,
            }
        return {
            "check_type": "file_location",
            "expected_dir": str(Path(path).parent) + "/",
        }

    if claim_type == "naming_pattern":
        pattern = extracted.get("pattern", "")
        # Map naming conventions to regex patterns
        naming_regexes = {
            "PascalCase": r"^[A-Z][a-zA-Z0-9]*$",
            "camelCase": r"^[a-z][a-zA-Z0-9]*$",
            "snake_case": r"^[a-z][a-z0-9_]*$",
            "kebab-case": r"^[a-z][a-z0-9-]*$",
            "UPPER_SNAKE_CASE": r"^[A-Z][A-Z0-9_]*$",
            "SCREAMING_SNAKE_CASE": r"^[A-Z][A-Z0-9_]*$",
        }
        regex = naming_regexes.get(pattern, pattern)
        return {
            "check_type": "file_naming",
            "pattern": regex,
        }

    if claim_type == "import_rule":
        rule = extracted.get("rule", "")
        return {
            "check_type": "import_style",
            "pattern": rule,
        }

    if claim_type == "convention":
        rule = extracted.get("rule", "").lower()

        # Detect "no X" / "avoid X" → code_absence check
        if re.match(r"^(no |never |avoid |don'?t )", rule):
            # Try to extract what to check for
            anti_match = re.search(r"(no |never |avoid |don'?t )(use )?(.*)", rule)
            anti_subject = anti_match.group(3).strip() if anti_match else rule
            return {
                "check_type": "code_absence",
                "pattern": anti_subject,
            }

        # Detect "use X" / "always X" → code_pattern check
        check_pattern = extracted.get("check_pattern")
        if check_pattern:
            return {
                "check_type": "code_pattern",
                "pattern": check_pattern,
            }

        return {
            "check_type": "code_pattern",
            "pattern": "",  # Agent will fill this
        }

    if claim_type == "architecture":
        return {
            "check_type": "code_pattern",
            "pattern": "",  # Agent will fill this
        }

    return {
        "check_type": "code_pattern",
        "pattern": "",
    }


# ---------------------------------------------------------------------------
# Task generation pipeline
# ---------------------------------------------------------------------------


def filter_eligible_claims(claims: list[dict], coherence_results: list[dict]) -> list[dict]:
    """Filter claims to those eligible for eval tasks."""
    # Build status lookup from coherence report
    status_map = {r["claim_id"]: r["status"] for r in coherence_results}

    eligible = []
    for claim in claims:
        # Must be a testable type
        if claim["type"] not in TESTABLE_TYPES:
            continue
        # Must be testable
        if not claim.get("testable", True):
            continue
        # Must be verified or partial in coherence (not stale)
        status = status_map.get(claim["id"], "unknown")
        if status not in ("verified", "partial", "unverifiable"):
            continue

        eligible.append(claim)

    return eligible


def group_claims(claims: list[dict]) -> list[list[dict]]:
    """Group related claims that can be tested together."""
    # Group by section first
    section_groups: dict[str, list[dict]] = {}
    for claim in claims:
        key = _section_key(claim)
        section_groups.setdefault(key, []).append(claim)

    # If too many groups, merge small ones
    groups = list(section_groups.values())

    # Split groups larger than 4 claims
    split_groups = []
    for group in groups:
        if len(group) <= 4:
            split_groups.append(group)
        else:
            # Split into chunks of 2-3
            for i in range(0, len(group), 3):
                chunk = group[i:i + 3]
                if chunk:
                    split_groups.append(chunk)

    # Merge groups smaller than 2 claims
    merged = []
    small_buffer: list[dict] = []
    for group in split_groups:
        if len(group) < 2:
            small_buffer.extend(group)
            if len(small_buffer) >= 2:
                merged.append(small_buffer[:3])
                small_buffer = small_buffer[3:]
        else:
            merged.append(group)

    if small_buffer:
        if merged:
            merged[-1].extend(small_buffer)
        else:
            merged.append(small_buffer)

    # Enforce MIN/MAX bounds
    if len(merged) > MAX_TASKS:
        # Combine excess groups
        while len(merged) > MAX_TASKS:
            smallest = min(range(len(merged)), key=lambda i: len(merged[i]))
            target = (smallest + 1) % len(merged) if smallest + 1 < len(merged) else smallest - 1
            if target < 0:
                break
            merged[target].extend(merged.pop(smallest))

    return merged


def generate_task_skeleton(task_id: int, claim_group: list[dict]) -> dict:
    """Generate a single eval task skeleton from a group of claims."""
    # Determine which claims are tested
    tests_claims = [c["id"] for c in claim_group]

    # Build description from claim types
    claim_types = set(c["type"] for c in claim_group)
    section_names = set(c.get("source_section", "Unknown") for c in claim_group)
    description = f"Tests {', '.join(sorted(claim_types))} from {', '.join(sorted(section_names))}"

    # Generate expected behaviors
    expected_behaviors = []
    for claim in claim_group:
        check_info = _infer_check_type(claim)
        expected_behaviors.append({
            "claim_id": claim["id"],
            "description": claim["raw_text"][:100],
            **check_info,
        })

    return {
        "id": f"task-{task_id}",
        "tests_claims": tests_claims,
        "description": description,
        "task_prompt": "",  # Agent fills this with a natural coding task
        "expected_behaviors": expected_behaviors,
    }


def generate_eval_tasks(claims_data: dict, coherence_data: dict, project_root: str) -> dict:
    """Generate the eval_tasks.json skeleton."""
    eligible = filter_eligible_claims(
        claims_data["claims"],
        coherence_data.get("results", []),
    )

    if not eligible:
        return {
            "project_root": project_root,
            "total_tasks": 0,
            "tasks": [],
            "note": "No eligible claims found for eval task generation",
        }

    groups = group_claims(eligible)
    tasks = []
    for i, group in enumerate(groups, 1):
        task = generate_task_skeleton(i, group)
        tasks.append(task)

    return {
        "project_root": project_root,
        "total_tasks": len(tasks),
        "eligible_claims": len(eligible),
        "tasks": tasks,
    }


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main():
    parser = argparse.ArgumentParser(description="Generate eval task skeletons from claims")
    parser.add_argument("claims_json", type=Path, help="Path to claims.json")
    parser.add_argument("coherence_json", type=Path, help="Path to coherence_report.json")
    parser.add_argument("project_root", type=str, help="Project root path")
    parser.add_argument("--output", type=Path, default=None)
    parser.add_argument("--pretty", action="store_true")
    args = parser.parse_args()

    claims_data = json.loads(args.claims_json.read_text(encoding="utf-8"))
    coherence_data = json.loads(args.coherence_json.read_text(encoding="utf-8"))

    result = generate_eval_tasks(claims_data, coherence_data, args.project_root)

    output_json = json.dumps(result, indent=2 if args.pretty else None, ensure_ascii=False)

    if args.output:
        args.output.write_text(output_json, encoding="utf-8")
        print(f"Generated {result['total_tasks']} eval task skeletons → {args.output}")
        print(f"Eligible claims: {result.get('eligible_claims', 0)}")
    else:
        print(output_json)


if __name__ == "__main__":
    main()
