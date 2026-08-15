"""Tests for the repo-wide validation sweep (validate_all.py)."""

import sys
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent.parent / "scripts"
sys.path.insert(0, str(SCRIPTS_DIR))

from validate_all import main, sweep  # noqa: E402

VALID_SKILL = """\
---
name: sample-skill
description: A minimal valid skill used in tests.
---

# Sample Skill

Small body.
"""


def _write_skill(skills_dir: Path, name: str, content: str) -> None:
    d = skills_dir / name
    d.mkdir(parents=True, exist_ok=True)
    (d / "SKILL.md").write_text(content, encoding="utf-8")


def test_sweep_all_valid(tmp_path):
    skills_dir = tmp_path / "skills"
    for i in range(2):
        _write_skill(skills_dir, f"skill-{i}", VALID_SKILL)
    results = sweep(skills_dir, strict=True, max_lines=500, max_tokens=5000, max_payload_tokens=20000)
    assert len(results) == 2
    assert all(r.valid for r in results)


def test_sweep_flags_oversized_skill(tmp_path):
    skills_dir = tmp_path / "skills"
    _write_skill(skills_dir, "good-skill", VALID_SKILL)
    bloated = VALID_SKILL + ("# Padding\n\n" * 2000)  # ~24k chars -> over the 5k-token budget
    _write_skill(skills_dir, "bloated-skill", bloated)

    results = sweep(skills_dir, strict=True, max_lines=500, max_tokens=5000, max_payload_tokens=20000)
    by_name = {r.skill_path.name: r for r in results}
    assert by_name["good-skill"].valid
    assert not by_name["bloated-skill"].valid


def test_sweep_ignores_non_skill_dirs(tmp_path):
    skills_dir = tmp_path / "skills"
    _write_skill(skills_dir, "real-skill", VALID_SKILL)
    (skills_dir / "not-a-skill").mkdir()  # no SKILL.md
    (skills_dir / "assets").mkdir()  # no SKILL.md
    results = sweep(skills_dir, strict=True, max_lines=500, max_tokens=5000, max_payload_tokens=20000)
    assert [r.skill_path.name for r in results] == ["real-skill"]


def test_main_exit_code_reflects_sweep(tmp_path):
    skills_dir = tmp_path / "skills"
    _write_skill(skills_dir, "ok-skill", VALID_SKILL)
    assert main(["--skills-dir", str(skills_dir), "--strict"]) == 0

    _write_skill(skills_dir, "bad-skill", VALID_SKILL + ("# Pad\n\n" * 3000))
    assert main(["--skills-dir", str(skills_dir), "--strict"]) == 1


def test_main_json_output(tmp_path, capsys):
    skills_dir = tmp_path / "skills"
    _write_skill(skills_dir, "ok-skill", VALID_SKILL)
    code = main(["--skills-dir", str(skills_dir), "--strict", "--json"])
    out = capsys.readouterr().out
    import json

    payload = json.loads(out)
    assert code == 0
    assert payload["all_valid"] is True
    assert payload["results"][0]["skill"] == "ok-skill"
    assert payload["results"][0]["valid"] is True
