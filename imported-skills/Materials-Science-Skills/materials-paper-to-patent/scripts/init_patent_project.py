#!/usr/bin/env python3
"""Create an agent-neutral materials-paper-to-patent project workspace."""

import argparse
import json
import shutil
from pathlib import Path


DIRECTORIES = (
    "paper",
    "supplementary/source-code",
    "source-figures",
    "existing-patent",
    "work",
    "outputs",
)
SKILL_FILES = ("SKILL.md", "manifest.yaml", "requirements.txt")
SKILL_DIRECTORIES = ("static", "references", "scripts")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("project_dir", type=Path)
    parser.add_argument("--paper", type=Path, help="Optional paper to copy into paper/")
    parser.add_argument("--force", action="store_true", help="Allow an existing project directory")
    parser.add_argument(
        "--no-embed-skill",
        action="store_true",
        help="Create only case directories without copying the skill bundle",
    )
    args = parser.parse_args()

    project = args.project_dir.resolve()
    if project.exists() and any(project.iterdir()) and not args.force:
        parser.error("project directory is not empty; use --force to add missing structure")
    project.mkdir(parents=True, exist_ok=True)
    for directory in DIRECTORIES:
        (project / directory).mkdir(parents=True, exist_ok=True)

    if not args.no_embed_skill:
        skill_root = Path(__file__).resolve().parents[1]
        if project != skill_root:
            for filename in SKILL_FILES:
                shutil.copy2(skill_root / filename, project / filename)
            for directory in SKILL_DIRECTORIES:
                shutil.copytree(
                    skill_root / directory,
                    project / directory,
                    dirs_exist_ok=True,
                    ignore=shutil.ignore_patterns("__pycache__", "*.pyc"),
                )

    if args.paper:
        paper = args.paper.resolve()
        if not paper.is_file():
            parser.error(f"paper does not exist: {paper}")
        shutil.copy2(paper, project / "paper" / paper.name)

    intake = {
        "target_jurisdiction": "中国发明专利",
        "requested_deliverable": "full-draft",
        "publication_status": "[TO CONFIRM: 论文是否已经公开]",
        "publication_dates": [],
        "inventorship": "[TO CONFIRM: 按实际技术贡献确认发明人]",
        "ownership": "[TO CONFIRM: 确认申请人和权属]",
        "source_files": [],
    }
    intake_path = project / "work" / "00-intake.json"
    if not intake_path.exists():
        intake_path.write_text(
            json.dumps(intake, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )

    notes = project / "supplementary" / "inventor-notes.md"
    if not notes.exists():
        notes.write_text(
            "# 发明人补充说明\n\n"
            "- 实际技术贡献：\n"
            "- 与论文不同的工程实现：\n"
            "- 可替代方案和参数范围：\n"
            "- 首次公开时间与方式：\n"
            "- 希望重点保护的内容：\n",
            encoding="utf-8",
        )

    print(project)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
