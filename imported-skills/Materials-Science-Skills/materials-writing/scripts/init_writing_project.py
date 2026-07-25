#!/usr/bin/env python3
"""Initialize a materials-writing foundation project."""

from __future__ import annotations

import argparse
import json
import shutil
import sys
from pathlib import Path
from typing import Any


SKILL_ROOT = Path(__file__).resolve().parents[1]
TEMPLATE_ROOT = SKILL_ROOT / "assets" / "templates" / "foundation"
FOUNDATION_FILES = [
    "00_scope.md",
    "01_research_canon.md",
    "02_evidence_table.md",
    "03_argument_map.md",
    "04_section_contracts.md",
    "05_style_guide.md",
]
STANDARD_DIRS = ["sources", "drafts", "revision_briefs", "qa_logs", "exports"]
WRITING_MODES = ("compose", "revise", "hybrid", "qa")


def _copy_template(src: Path, dst: Path, force: bool) -> None:
    if dst.exists() and not force:
        raise FileExistsError(f"refusing to overwrite existing file: {dst}")
    shutil.copyfile(src, dst)


def _load_state_template() -> dict[str, Any]:
    template_path = TEMPLATE_ROOT / "state-template.json"
    return json.loads(template_path.read_text(encoding="utf-8"))


def initialize_project(
    target: str | Path,
    project_title: str = "Untitled materials writing project",
    writing_mode: str = "compose",
    force: bool = False,
) -> Path:
    """Create foundation files and return the generated state path."""

    if writing_mode not in WRITING_MODES:
        raise ValueError(f"writing_mode must be one of: {', '.join(WRITING_MODES)}")

    target_path = Path(target)
    target_path.mkdir(parents=True, exist_ok=True)

    for dirname in STANDARD_DIRS:
        directory = target_path / dirname
        if directory.exists() and not directory.is_dir():
            raise FileExistsError(f"expected directory but found file: {directory}")
        directory.mkdir(exist_ok=True)

    for filename in FOUNDATION_FILES:
        _copy_template(TEMPLATE_ROOT / filename, target_path / filename, force)

    state_path = target_path / "state.json"
    if state_path.exists() and not force:
        raise FileExistsError(f"refusing to overwrite existing file: {state_path}")

    state = _load_state_template()
    state["writing_mode"] = writing_mode
    state["project"]["title"] = project_title
    state_path.write_text(json.dumps(state, indent=2) + "\n", encoding="utf-8")
    return state_path


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", required=True, help="Directory for the writing project.")
    parser.add_argument(
        "--project-title",
        default="Untitled materials writing project",
        help="Title stored in state.json.",
    )
    parser.add_argument(
        "--writing-mode",
        choices=WRITING_MODES,
        default="compose",
        help="Initial writing mode stored in state.json.",
    )
    parser.add_argument("--force", action="store_true", help="Allow overwriting existing files.")
    args = parser.parse_args(argv)

    try:
        state_path = initialize_project(
            args.target,
            project_title=args.project_title,
            writing_mode=args.writing_mode,
            force=args.force,
        )
    except (FileExistsError, ValueError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2

    print(state_path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
