import sys
from pathlib import Path

import pytest


SKILL_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SKILL_ROOT))

from scripts import run_loop as loop_module  # noqa: E402


def test_small_stratified_set_keeps_both_classes_in_training(monkeypatch, tmp_path):
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
