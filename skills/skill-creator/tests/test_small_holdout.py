import sys
from pathlib import Path

import pytest


SKILL_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SKILL_ROOT))

from scripts import run_loop as loop_module  # noqa: E402


def test_small_stratified_set_keeps_both_classes_in_training(monkeypatch, tmp_path, capsys):
    eval_set = [
        {"query": "relevant request", "should_trigger": True},
        {"query": "unrelated request", "should_trigger": False},
    ]
    monkeypatch.setattr(loop_module, "find_project_root", lambda: tmp_path)
    monkeypatch.setattr(
        loop_module, "parse_skill_md", lambda path: ("example", "original", "content")
    )

    def fake_run_eval(**kwargs):
        return {
            "results": [
                {
                    **item,
                    "pass": False,
                    "triggers": 0,
                    "runs": 1,
                }
                for item in kwargs["eval_set"]
            ]
        }

    monkeypatch.setattr(loop_module, "run_eval", fake_run_eval)

    result = loop_module.run_loop(
        eval_set=eval_set,
        skill_path=tmp_path,
        description_override=None,
        num_workers=1,
        timeout=1,
        max_iterations=1,
        runs_per_query=1,
        trigger_threshold=0.5,
        holdout=0.4,
        model="test-model",
        verbose=False,
    )

    assert result["history"][0]["train_total"] == 2
    assert result["history"][0]["test_total"] is None
    assert result["exit_reason"] == "max_iterations (1)"
    assert "no held-out score" in capsys.readouterr().err


def test_empty_eval_set_does_not_report_success(tmp_path):
    with pytest.raises(ValueError, match="at least one query"):
        loop_module.run_loop(
            eval_set=[],
            skill_path=tmp_path,
            description_override=None,
            num_workers=1,
            timeout=1,
            max_iterations=1,
            runs_per_query=1,
            trigger_threshold=0.5,
            holdout=0.4,
            model="test-model",
            verbose=False,
        )


def test_cli_explains_empty_eval_set_without_opening_report(monkeypatch, tmp_path, capsys):
    eval_file = tmp_path / "empty.json"
    eval_file.write_text("[]")
    skill = tmp_path / "skill"
    skill.mkdir()
    (skill / "SKILL.md").write_text("---\nname: sample\ndescription: Sample\n---\n")
    monkeypatch.setattr(loop_module, "parse_skill_md", lambda path: ("sample", "Sample", ""))
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "run_loop.py",
            "--eval-set", str(eval_file),
            "--skill-path", str(skill),
            "--model", "test-model",
            "--report", "none",
        ],
    )

    with pytest.raises(SystemExit) as exc:
        loop_module.main()
    assert exc.value.code == 2
    assert "Eval set must contain at least one query" in capsys.readouterr().err
