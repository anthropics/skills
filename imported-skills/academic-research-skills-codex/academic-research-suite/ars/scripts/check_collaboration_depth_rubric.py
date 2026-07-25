#!/usr/bin/env python3
"""Validate the Collaboration Depth Observer artifacts (ARS v3.5).

Usage: python scripts/check_collaboration_depth_rubric.py [--path REPO_ROOT]
Exit codes: 0 all checks pass; 1 at least one check failed.
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

from _skill_lint import split_frontmatter

RUBRIC_PATH = Path("shared/collaboration_depth_rubric.md")
ORCHESTRATOR_PATH = Path("academic-pipeline/agents/pipeline_orchestrator_agent.md")
PIPELINE_SKILL_PATH = Path("academic-pipeline/SKILL.md")
AGENTS_DIR = Path("academic-pipeline/agents")

DOI_TOKEN = "10.1186/s41239-026-00585-x"
CANONICAL_DIMENSIONS = (
    "Delegation Intensity",
    "Cognitive Vigilance",
    "Cognitive Reallocation",
    "Zone Classification",
)
CHECKPOINT_TOKENS = ("FULL checkpoint", "SLIM checkpoint", "checkpoint")
COMPLETION_TOKENS = ("pipeline completion", "pipeline end", "stage 6")
# Dispatch verbs + the agent name, matched on the same line (case-insensitive).
# Keyword presence alone is not enough: the orchestrator must actually say it
# dispatches the observer at checkpoints and at pipeline completion.
DISPATCH_VERBS = ("dispatch", "invoke", "invocation", "call", "run")
_VERBS = "|".join(DISPATCH_VERBS)
# Dispatch verb and agent name within ~80 chars of each other, either order,
# allowed to span a line break (writers naturally wrap "dispatch\nagent_name").
DISPATCH_RE = re.compile(
    rf"(?is)\b(?:{_VERBS})\b.{{0,80}}?\bcollaboration_depth_agent\b"
    rf"|\bcollaboration_depth_agent\b.{{0,80}}?\b(?:{_VERBS})\b"
)
NON_BLOCKING_PHRASES = (
    "never blocks",
    "does not block",
    "advisory only",
    "advisory-only",
    "non-blocking",
    "blocking: false",
)


def _check_rubric(root: Path) -> list[str]:
    errs: list[str] = []
    path = root / RUBRIC_PATH
    if not path.is_file():
        return [f"{RUBRIC_PATH} does not exist"]
    text = path.read_text(encoding="utf-8")

    if "Wang" not in text or "2026" not in text or DOI_TOKEN not in text:
        errs.append(
            f"{RUBRIC_PATH}: must cite Wang & Zhang (2026) including DOI {DOI_TOKEN}"
        )

    fm, body = split_frontmatter(text)
    if fm is None:
        errs.append(f"{RUBRIC_PATH}: missing or unparseable YAML frontmatter")
        return errs
    if "rubric_version" not in fm:
        errs.append(f"{RUBRIC_PATH}: frontmatter missing 'rubric_version' field")

    for dim in CANONICAL_DIMENSIONS:
        if not re.search(rf"(?m)^#{{1,6}}\s+.*\b{re.escape(dim)}\b", body):
            errs.append(f"{RUBRIC_PATH}: missing canonical dimension heading '{dim}'")
    return errs


def _check_agent_files(root: Path) -> list[str]:
    agents_dir = root / AGENTS_DIR
    if not agents_dir.is_dir():
        return [f"{AGENTS_DIR} does not exist"]
    errs: list[str] = []
    rubric_path_str = str(RUBRIC_PATH)
    for path in sorted(agents_dir.glob("*.md")):
        text = path.read_text(encoding="utf-8")
        fm, _ = split_frontmatter(text)
        if fm is None or fm.get("measures") != "collaboration_depth":
            continue
        rel = path.relative_to(root)
        # rubric_ref is the machine-readable contract. Body text is documentation.
        ref = fm.get("rubric_ref")
        if ref != rubric_path_str:
            errs.append(
                f"{rel}: frontmatter rubric_ref={ref!r} must equal "
                f"{rubric_path_str!r} (canonical rubric path)"
            )
        if fm.get("blocking") is not False:
            errs.append(
                f"{rel}: declares measures=collaboration_depth but "
                f"'blocking' is not false (observer must never block)"
            )
    return errs


def _check_orchestrator(root: Path) -> list[str]:
    path = root / ORCHESTRATOR_PATH
    if not path.is_file():
        return [f"{ORCHESTRATOR_PATH} does not exist"]
    text = path.read_text(encoding="utf-8")
    if "collaboration_depth_agent" not in text:
        return [f"{ORCHESTRATOR_PATH}: does not mention 'collaboration_depth_agent'"]

    # Require a real dispatch anchor: a dispatch verb on the same line as the
    # agent name. Bare keyword presence isn't enough — the orchestrator may
    # reference the agent in a roster or an anti-pattern paragraph without
    # actually saying it dispatches the agent at checkpoints.
    if not DISPATCH_RE.search(text):
        return [
            f"{ORCHESTRATOR_PATH}: mentions collaboration_depth_agent but "
            f"no dispatch anchor (e.g. 'dispatch collaboration_depth_agent', "
            f"'invoke collaboration_depth_agent')"
        ]

    errs: list[str] = []
    if not any(tok in text for tok in CHECKPOINT_TOKENS):
        errs.append(
            f"{ORCHESTRATOR_PATH}: mentions collaboration_depth_agent but "
            f"no checkpoint invocation context"
        )
    lower = text.lower()
    if not any(tok in lower for tok in COMPLETION_TOKENS):
        errs.append(
            f"{ORCHESTRATOR_PATH}: mentions collaboration_depth_agent but "
            f"no pipeline-completion invocation context"
        )
    return errs


def _check_skill_md(root: Path) -> list[str]:
    rel_path = (
        Path("academic-pipeline/WORKFLOW.md")
        if (root / "academic-pipeline/WORKFLOW.md").is_file()
        else PIPELINE_SKILL_PATH
    )
    path = root / rel_path
    if not path.is_file():
        return [f"{rel_path} does not exist"]
    text = path.read_text(encoding="utf-8").lower()
    if "collaboration_depth_agent" not in text:
        return [f"{rel_path}: does not mention collaboration_depth_agent"]
    if not any(p in text for p in NON_BLOCKING_PHRASES):
        return [
            f"{rel_path}: observer invocation must be explicitly "
            f"described as non-blocking (e.g. 'never blocks', 'advisory only')"
        ]
    return []


def run_checks(root: Path) -> list[str]:
    return (
        _check_rubric(root)
        + _check_agent_files(root)
        + _check_orchestrator(root)
        + _check_skill_md(root)
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--path",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
    )
    args = parser.parse_args()
    violations = run_checks(args.path)
    if violations:
        for v in violations:
            print(f"ERROR: {v}")
        print(f"\n{len(violations)} violation(s) found.", file=sys.stderr)
        return 1
    print("collaboration_depth_rubric: OK")
    return 0


if __name__ == "__main__":
    sys.exit(main())
